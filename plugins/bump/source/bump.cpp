#include "gideros.h"
#include "lua.h"
#include "lauxlib.h"
#include <math.h>
#include <map>
#include <set>
#include <algorithm>
//#include <QDebug>

#define UNUSED(x) (void)(x)

#define MATH_HUGE HUGE_VAL
/*
 local bump = {
 _VERSION     = 'bump v3.1.7',
 _URL         = 'https://github.com/kikito/bump.lua',
 _DESCRIPTION = 'A collision detection library for Lua',
 _LICENSE     = [[
 MIT LICENSE

 Copyright (c) 2014 Enrique Garc�a Cota

 Permission is hereby granted, free of charge, to any person obtaining a
 copy of this software and associated documentation files (the
 "Software"), to deal in the Software without restriction, including
 without limitation the rights to use, copy, modify, merge, publish,
 distribute, sublicense, and/or sell copies of the Software, and to
 permit persons to whom the Software is furnished to do so, subject to
 the following conditions:

 The above copyright notice and this permission notice shall be included
 in all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ]]
 }*/

#define DELTA 1e-10 // -- floating-point margin of error

#define iabs(a) ((a>=0)?a:-a)
static double sign(double x) {
	return (x > 0) ? 1 : ((x == 0) ? 0 : -1);
}
static double nearest(double x, double a, double b) {
	return fabs(a - x) < fabs(b - x) ? a : b;
}

static const char *luaL_tostring(lua_State *L,int narg)
{
	lua_getglobal(L, "tostring");
	lua_pushvalue(L,narg);
	lua_call(L, 1, 1);
	const char *str=lua_tostring(L,-1);
	lua_pop(L,1);
	return str;
}

static void assertNumber(lua_State *L, int narg, const char *name) {
    lua_Number d = lua_tonumber(L, narg);
	if (d == 0 && !lua_isnumber(L, narg)) /* avoid extra test when d is not 0 */
	{
		lua_pushfstring(L, "%s must be a number, but was %s (a %s)", name,
				luaL_tostring(L, narg), lua_typename(L, narg));
		lua_error(L);
	}
}

static void assertIsPositiveNumber(lua_State *L, int narg, const char *name) {
    lua_Number d = lua_tonumber(L, narg);
	if (d <= 0) {
		lua_pushfstring(L, "%s must be a positive integer, but was %s (a %s)",
				name, luaL_tostring(L, narg), lua_typename(L, narg));
		lua_error(L);
	}
}

static void assertIsRect(lua_State *L, int x, int y, int w, int h) {
	assertNumber(L, x, "x");
	assertNumber(L, y, "y");
	assertIsPositiveNumber(L, w, "w");
	assertIsPositiveNumber(L, h, "h");
}

static void assertIsCube(lua_State *L, int x, int y, int z, int w, int h,int d) {
	assertNumber(L, x, "x");
	assertNumber(L, y, "y");
	assertNumber(L, z, "z");
	assertIsPositiveNumber(L, w, "w");
	assertIsPositiveNumber(L, h, "h");
	assertIsPositiveNumber(L, d, "d");
}

struct ColFilter {
	virtual const char *Filter(int item, int other)=0;
	virtual ~ColFilter() { };
};

struct defaultFilter: ColFilter {
	const char *Filter(int item, int other) { UNUSED(item); UNUSED(other);
		return "slide";
	}
	;
};

/*
 ------------------------------------------
 -- Rectangle functions
 ------------------------------------------
 */

static void rect_getNearestCorner(double x, double y, double w, double h,
		double px, double py, double &nx, double &ny) {
	nx = nearest(px, x, x + w);
	ny = nearest(py, y, y + h);
}

/*-- This is a generalized implementation of the liang-barsky algorithm, which also returns
 -- the normals of the sides where the segment intersects.
 -- Returns nil if the segment never touches the rect
 -- Notice that normals are only guaranteed to be accurate when initially ti1, ti2 == -math.huge, math.huge
 */
static bool rect_getSegmentIntersectionIndices(double x, double y, double w,
		double h, double x1, double y1, double x2, double y2, double &ti1,
		double &ti2, double &nx1, double &ny1, double &nx2, double &ny2) {
	//ti1, ti2 = ti1 or 0, ti2 or 1 TODO
	double dx = x2 - x1;
	double dy = y2 - y1;
	double nx, ny;
	double p, q, r;
	nx1 = nx2 = ny1 = ny2 = 0;

	for (int side = 1; side <= 4; side++) {
		switch (side) {
		case 1:
			nx = -1;
			ny = 0;
			p = -dx;
			q = x1 - x;
			break; //-- left
		case 2:
			nx = 1;
			ny = 0;
			p = dx;
			q = x + w - x1;
			break; //-- right
		case 3:
			nx = 0;
			ny = -1;
			p = -dy;
			q = y1 - y;
			break; //-- top
		case 4:
			nx = 0;
			ny = 1;
			p = dy;
			q = y + h - y1;
			break; //-- bottom
		}
		if (p == 0) {
			if (q <= 0)
				return false;
		} else {
			r = q / p;
			if (p < 0) {
				if (r > ti2)
					return false;
				if (r > ti1) {
					ti1 = r;
					nx1 = nx;
					ny1 = ny;
				}
			} else { //-- p > 0
				if (r < ti1)
					return false;
				if (r < ti2) {
					ti2 = r;
					nx2 = nx;
					ny2 = ny;
				}
			}
		}
	}
	return true;
}

//-- Calculates the minkowsky difference between 2 rects, which is another rect
static void rect_getDiff(double x1, double y1, double w1, double h1, double x2,
		double y2, double w2, double h2, double &rx, double &ry, double &rw,
		double &rh) {
	rx = x2 - x1 - w1;
	ry = y2 - y1 - h1;
	rw = w1 + w2;
	rh = h1 + h2;
}

static bool rect_containsPoint(double x, double y, double w, double h,
		double px, double py) {
	return ((px - x) > DELTA) && ((py - y) > DELTA) && ((x + w - px) > DELTA)
			&& ((y + h - py) > DELTA);
}

static bool rect_isIntersecting(double x1, double y1, double w1, double h1,
		double x2, double y2, double w2, double h2) {
	return (x1 < (x2 + w2)) && (x2 < (x1 + w1)) && (y1 < (y2 + h2))
			&& (y2 < (y1 + h1));
}

static double rect_getSquareDistance(double x1, double y1, double w1, double h1,
		double x2, double y2, double w2, double h2) {
	double dx = x1 - x2 + (w1 - w2) / 2;
	double dy = y1 - y2 + (h1 - h2) / 2;
	return dx * dx + dy * dy;
}


/*
 ------------------------------------------
 -- Cube functions
 ------------------------------------------
 */

static void cube_getNearestCorner(double x, double y, double z, double w, double h, double d,
		double px, double py, double pz, double &nx, double &ny, double &nz) {
	nx = nearest(px, x, x + w);
	ny = nearest(py, y, y + h);
	nz = nearest(pz, z, z + d);
}

/*-- This is a generalized implementation of the liang-barsky algorithm, which also returns
 -- the normals of the sides where the segment intersects.
 -- Returns nil if the segment never touches the rect
 -- Notice that normals are only guaranteed to be accurate when initially ti1, ti2 == -math.huge, math.huge
 */
static bool cube_getSegmentIntersectionIndices(double x, double y, double z,
		double w, double h, double d,
		double x1, double y1, double z1, double x2, double y2, double z2,
		double &ti1, double &ti2,
		double &nx1, double &ny1, double &nz1, double &nx2, double &ny2, double &nz2) {
	//ti1, ti2 = ti1 or 0, ti2 or 1 TODO
	double dx = x2 - x1;
	double dy = y2 - y1;
	double dz = z2 - z1;
	double nx, ny, nz;
	double p, q, r;
	nx1 = nx2 = ny1 = ny2 = nz1 = nz2 = 0;

	for (int side = 1; side <= 6; side++) {
		switch (side) {
		case 1:
			nx = -1;
			ny = 0;
			nz = 0;
			p = -dx;
			q = x1 - x;
			break; //-- left
		case 2:
			nx = 1;
			ny = 0;
			nz = 0;
			p = dx;
			q = x + w - x1;
			break; //-- right
		case 3:
			nx = 0;
			ny = -1;
			nz = 0;
			p = -dy;
			q = y1 - y;
			break; //-- top
		case 4:
			nx = 0;
			ny = 1;
			nz = 0;
			p = dy;
			q = y + h - y1;
			break; //-- bottom
		case 5:
			nx = 0;
			ny = 0;
			nz = -1;
			p = -dz;
			q = z1 - z;
			break; //-- front
		case 6:
			nx = 0;
			ny = 0;
			nz = 1;
			p = dz;
			q = z + d - z1;
			break; //-- back
		}
		if (p == 0) {
			if (q <= 0)
				return false;
		} else {
			r = q / p;
			if (p < 0) {
				if (r > ti2)
					return false;
				if (r > ti1) {
					ti1 = r;
					nx1 = nx;
					ny1 = ny;
					nz1 = nz;
				}
			} else { //-- p > 0
				if (r < ti1)
					return false;
				if (r < ti2) {
					ti2 = r;
					nx2 = nx;
					ny2 = ny;
					nz2 = nz;
				}
			}
		}
	}
	return true;
}

//-- Calculates the minkowsky difference between 2 rects, which is another rect
static void cube_getDiff(double x1, double y1, double z1, double w1, double h1, double d1,
		double x2,	double y2, double z2, double w2, double h2, double d2,
		double &rx, double &ry, double &rz, double &rw,	double &rh, double &rd) {
	rx = x2 - x1 - w1;
	ry = y2 - y1 - h1;
	rz = z2 - z1 - d1;
	rw = w1 + w2;
	rh = h1 + h2;
	rd = d1 + d2;
}

static bool cube_containsPoint(double x, double y, double z, double w, double h, double d,
		double px, double py, double pz) {
	return ((px - x) > DELTA) && ((py - y) > DELTA) && ((pz - z) > DELTA) &&
			((x + w - px) > DELTA) && ((y + h - py) > DELTA) && ((z + d - pz) > DELTA);
}

static bool cube_isIntersecting(double x1, double y1, double z1, double w1, double h1, double d1,
		double x2, double y2, double z2, double w2, double h2, double d2) {
	return (x1 < (x2 + w2)) && (x2 < (x1 + w1)) &&
			(y1 < (y2 + h2)) && (y2 < (y1 + h1)) &&
			(z1 < (z2 + d2)) && (z2 < (z1 + d1));
}

static double cube_getCubeDistance(double x1, double y1, double z1, double w1, double h1, double d1,
		double x2, double y2, double z2, double w2, double h2, double d2) {
	double dx = x1 - x2 + (w1 - w2) / 2;
	double dy = y1 - y2 + (h1 - h2) / 2;
	double dz = z1 - z2 + (d1 - d2) / 2;
	return dx * dx + dy * dy + dz * dz;
}

struct Point {
	double x, y, z;
};
struct Rect {
	double x, y, z, w, h, d;
};
struct Collision {
	bool overlaps;
	int item;
	int other;
	const char *type;
	double ti;
	double distance;
	Point move, normal, touch;
	Point response;
	Rect itemRect, otherRect;
};

static bool rect_detectCollision(double x1, double y1, double w1, double h1,
		double x2, double y2, double w2, double h2, double goalX, double goalY,
		Collision &col) {
	//goalX = goalX or x1 TODO
	//goalY = goalY or y1

	double dx = goalX - x1, dy = goalY - y1;
	double x, y, w, h;
	rect_getDiff(x1, y1, w1, h1, x2, y2, w2, h2, x, y, w, h);

	bool overlaps=false;
	double ti;
	bool cf = false;
	double nx=0, ny=0;

	if (rect_containsPoint(x, y, w, h, 0, 0)) { //-- item was intersecting other
		double px, py;
		rect_getNearestCorner(x, y, w, h, 0, 0, px, py);
		double wi = (w1 < fabs(px)) ? w1 : fabs(px);
		double hi = (h1 < fabs(py)) ? h1 : fabs(py);
		ti = -wi * hi; //-- ti is the negative area of intersection
		overlaps = true;
		cf = true;
	} else {
		double ti1 = -MATH_HUGE, ti2 = MATH_HUGE;
		double nx1, ny1, nx2, ny2;
		if (rect_getSegmentIntersectionIndices(x, y, w, h, 0, 0, dx, dy, ti1,
				ti2, nx1, ny1, nx2, ny2)) {
			//-- item tunnels into other
			if ((ti1 < 1) && (fabs(ti1 - ti2) >= DELTA) //-- special case for rect going through another rect's corner
					&& ((0 < (ti1 + DELTA)) || ((0 == ti1) && (ti2 > 0)))) {
				ti = ti1;
				nx = nx1;
				ny = ny1;
				overlaps = false;
				cf = true;
			}
		}
	}

	if (!cf)
		return false;

	double tx, ty;

	if (overlaps) {
		if ((dx == 0) && (dy == 0)) {
			//-- intersecting and not moving - use minimum displacement vector
			double px, py;
			rect_getNearestCorner(x, y, w, h, 0, 0, px, py);
			if (fabs(px) < fabs(py))
				py = 0;
			else
				px = 0;
			nx = sign(px);
			ny = sign(py);
			tx = x1 + px;
			ty = y1 + py;
		} else {
			//-- intersecting and moving - move in the opposite direction
			double ti1 = -MATH_HUGE;
			double ti2 = 1;
			double nx1, ny1, nx2, ny2;
			if (!rect_getSegmentIntersectionIndices(x, y, w, h, 0, 0, dx, dy,
					ti1, ti2, nx1, ny1, nx2, ny2))
				return false;
            nx = nx1;
            ny = ny1;
			tx = x1 + dx * ti1;
			ty = y1 + dy * ti1;
		}
	} else //-- tunnel
	{
		tx = x1 + dx * ti;
		ty = y1 + dy * ti;
	}

	col.overlaps = overlaps;
	col.ti = ti;
	col.distance = rect_getSquareDistance(x1,y1,w1,h1,x2,y2,w2,h2);
	col.move.x = dx;
	col.move.y = dy;
	col.normal.x = nx;
	col.normal.y = ny;
	col.touch.x = tx;
	col.touch.y = ty;
	col.itemRect.x = x1;
	col.itemRect.y = y1;
	col.itemRect.w = w1;
	col.itemRect.h = h1;
	col.otherRect.x = x2;
	col.otherRect.y = y2;
	col.otherRect.w = w2;
	col.otherRect.h = h2;
	return true;
}

static bool cube_detectCollision(double x1, double y1, double z1, double w1, double h1, double d1,
		double x2, double y2, double z2, double w2, double h2, double d2, double goalX, double goalY, double goalZ,
		Collision &col) {
	//goalX = goalX or x1 TODO
	//goalY = goalY or y1
	//goalZ = goalZ or z1

	double dx = goalX - x1, dy = goalY - y1, dz = goalZ - z1;
	double x, y, z, w, h, d;
	cube_getDiff(x1, y1, z1, w1, h1, d1, x2, y2, z2, w2, h2, d2, x, y, z, w, h, d);

	bool overlaps=false;
	double ti;
	bool cf = false;
	double nx=0, ny=0, nz=0;

	if (cube_containsPoint(x, y, z, w, h, d, 0, 0, 0)) { //-- item was intersecting other
		double px, py, pz;
		cube_getNearestCorner(x, y, z, w, h, d, 0, 0, 0, px, py, pz);
		double wi = (w1 < fabs(px)) ? w1 : fabs(px);
		double hi = (h1 < fabs(py)) ? h1 : fabs(py);
		double di = (d1 < fabs(pz)) ? d1 : fabs(pz);
		ti = -wi * hi * di; //-- ti is the negative area of intersection
		overlaps = true;
		cf = true;
	} else {
		double ti1 = -MATH_HUGE, ti2 = MATH_HUGE;
		double nx1, ny1, nz1, nx2, ny2, nz2;
		if (cube_getSegmentIntersectionIndices(x, y, z, w, h, d, 0, 0, 0, dx, dy, dz, ti1,
				ti2, nx1, ny1, nz1, nx2, ny2, nz2)) {
			//-- item tunnels into other
			if ((ti1 < 1) && (fabs(ti1 - ti2) >= DELTA) //-- special case for rect going through another rect's corner
					&& ((0 < (ti1 + DELTA)) || ((0 == ti1) && (ti2 > 0)))) {
                ti = ti1;
				nx = nx1;
				ny = ny1;
				nz = nz1;
				overlaps = false;
				cf = true;
			}
		}
	}

	if (!cf)
		return false;

	double tx, ty, tz;

	if (overlaps) {
		if ((dx == 0) && (dy == 0) && (dz==0)) {
			//-- intersecting and not moving - use minimum displacement vector
			double px, py, pz;
			cube_getNearestCorner(x, y, z, w, h, d, 0, 0, 0, px, py, pz);
			if ((fabs(px) <= fabs(py)) && (fabs(px) <= fabs(pz)))
			{
				py = 0;
				pz = 0;
			}
			else if (fabs(py)<=fabs(pz))
			{
				px = 0;
				pz = 0;
			}
			else
			{
				px = 0;
				py = 0;
			}
			nx = sign(px);
			ny = sign(py);
			nz = sign(pz);
			tx = x1 + px;
			ty = y1 + py;
			tz = z1 + pz;
		} else {
			//-- intersecting and moving - move in the opposite direction
			double ti1 = -MATH_HUGE;
			double ti2 = 1;
			double nx1, ny1, nz1, nx2, ny2, nz2;
			if (!cube_getSegmentIntersectionIndices(x, y, z, w, h, d, 0, 0, 0, dx, dy, dz,
					ti1, ti2, nx1, ny1, nz1, nx2, ny2, nz2))
				return false;
            nx = nx1;
            ny = ny1;
            nz = nz1;
			tx = x1 + dx * ti1;
			ty = y1 + dy * ti1;
			tz = z1 + dz * ti1;
        }
	} else //-- tunnel
	{
		tx = x1 + dx * ti;
		ty = y1 + dy * ti;
		tz = z1 + dz * ti;
	}

	col.overlaps = overlaps;
	col.ti = ti;
	col.distance = cube_getCubeDistance(x1,y1,z1,w1,h1,d1,x2,y2,z2,w2,h2,d2);
	col.move.x = dx;
	col.move.y = dy;
	col.move.z = dz;
	col.normal.x = nx;
	col.normal.y = ny;
	col.normal.z = nz;
	col.touch.x = tx;
	col.touch.y = ty;
	col.touch.z = tz;
	col.itemRect.x = x1;
	col.itemRect.y = y1;
	col.itemRect.z = z1;
	col.itemRect.w = w1;
	col.itemRect.h = h1;
	col.itemRect.d = d1;
	col.otherRect.x = x2;
	col.otherRect.y = y2;
	col.otherRect.z = z2;
	col.otherRect.w = w2;
	col.otherRect.h = h2;
	col.otherRect.d = d2;
	return true;
}

//------------------------------------------
//-- Grid functions
//------------------------------------------

static void grid_toWorld(int cellSize, int cx, int cy, double &wx, double &wy) {
	wx = (cx - 1) * cellSize;
	wy = (cy - 1) * cellSize;
}

static void grid_toCell(int cellSize, double x, double y, int &cx, int &cy) {
	cx = floor(x / cellSize) + 1;
	cy = floor(y / cellSize) + 1;
}

static void grid_toWorld3(int cellSize, int cx, int cy, int cz, double &wx, double &wy, double &wz) {
	wx = (cx - 1) * cellSize;
	wy = (cy - 1) * cellSize;
	wz = (cz - 1) * cellSize;
}

static void grid_toCell3(int cellSize, double x, double y, double z, int &cx, int &cy, int &cz) {
	cx = floor(x / cellSize) + 1;
	cy = floor(y / cellSize) + 1;
	cz = floor(z / cellSize) + 1;
}

/*-- grid_traverse* functions are based on "A Fast Voxel Traversal Algorithm for Ray Tracing",
 -- by John Amanides and Andrew Woo - http://www.cse.yorku.ca/~amana/research/grid.pdf
 -- It has been modified to include both cells when the ray "touches a grid corner",
 -- and with a different exit condition*/

static int grid_traverse_initStep(int cellSize, int ct, double t1, double t2,
		double &rx, double &ry) {
	double v = t2 - t1;
	if (v > 0) {
		rx = cellSize / v;
		ry = ((ct + v) * cellSize - t1) / v;
		return 1;
	}
	if (v < 0) {
		rx = -cellSize / v;
		ry = ((ct + v - 1) * cellSize - t1) / v;
		return -1;
	}
	rx = HUGE_VAL;
	ry = HUGE_VAL;
	return 0;
}

typedef void (*pointFunc)(void *data, int, int);
typedef void (*pointFunc3)(void *data, int, int, int);

static void grid_traverse(int cellSize, double x1, double y1, double x2,
		double y2, pointFunc f, void *data) {
	int cx1, cy1, cx2, cy2;
	double dx, tx, dy, ty;
	grid_toCell(cellSize, x1, y1, cx1, cy1);
	grid_toCell(cellSize, x2, y2, cx2, cy2);
	int stepX = grid_traverse_initStep(cellSize, cx1, x1, x2, dx, tx);
	int stepY = grid_traverse_initStep(cellSize, cy1, y1, y2, dy, ty);
	int cx = cx1;
	int cy = cy1;

	f(data, cx, cy);

	//-- The default implementation had an infinite loop problem when
	//-- approaching the last cell in some occassions. We finish iterating
	//-- when we are *next* to the last cell
	while ((iabs(cx - cx2) + iabs(cy - cy2)) > 1) {
		if (tx < ty) {
			tx += dx;
			cx += stepX;
			f(data, cx, cy);
		} else {
			//-- Addition: include both cells when going through corners
			if (tx == ty)
				f(data, cx + stepX, cy);
			ty += dy;
			cy += stepY;
			f(data, cx, cy);
		}
	}

	//-- If we have not arrived to the last cell, use it
	if ((cx != cx2) || (cy != cy2))
		f(data, cx2, cy2);
}

static void grid_toCellRect(int cellSize, double x, double y, double w,
		double h, int &cx, int &cy, int &cw, int &ch) {
	grid_toCell(cellSize, x, y, cx, cy);
	int cr = ceil((x + w) / cellSize);
	int cb = ceil((y + h) / cellSize);
	cw = cr - cx + 1;
	ch = cb - cy + 1;
}

static void grid_traverse3(int cellSize, double x1, double y1, double z1, double x2,
		double y2, double z2, pointFunc3 f, void *data) {
	int cx1, cy1, cz1, cx2, cy2, cz2;
	double dx, tx, dy, ty, dz, tz;
	grid_toCell3(cellSize, x1, y1, z1, cx1, cy1, cz1);
	grid_toCell3(cellSize, x2, y2, z2, cx2, cy2, cz2);
	int stepX = grid_traverse_initStep(cellSize, cx1, x1, x2, dx, tx);
	int stepY = grid_traverse_initStep(cellSize, cy1, y1, y2, dy, ty);
	int stepZ = grid_traverse_initStep(cellSize, cz1, z1, z2, dz, tz);
	int cx = cx1;
	int cy = cy1;
	int cz = cz1;

	f(data, cx, cy, cz);

	//-- The default implementation had an infinite loop problem when
	//-- approaching the last cell in some occassions. We finish iterating
	//-- when we are *next* to the last cell
	while ((iabs(cx - cx2) + iabs(cy - cy2) + iabs(cz - cz2)) > 1) {
		if ((tx < ty) && ( tx < tz)) {
			tx += dx;
			cx += stepX;
			f(data, cx, cy, cz);
		}
		else if (ty < tz) {
			//-- Addition: include both cells when going through corners
			if (tx == ty)
				f(data, cx + stepX, cy, cz);
			ty += dy;
			cy += stepY;
			f(data, cx, cy, cz);
		} else {
			//-- Addition: include both cells when going through corners
			if (tx == tz)
				f(data, cx + stepX, cy, cz);
			if (ty == tz)
				f(data, cx, cy + stepY, cz);
			tz += dz;
			cz += stepZ;
			f(data, cx, cy, cz);
		}
	}

	//-- If we have not arrived to the last cell, use it
	if ((cx != cx2) || (cy != cy2) || (cz != cz2))
		f(data, cx2, cy2, cz2);
}

static void grid_toCellCube(int cellSize, double x, double y, double z,
		double w, double h, double d,
		int &cx, int &cy, int &cz, int &cw, int &ch, int &cd) {
	grid_toCell3(cellSize, x, y, z, cx, cy, cz);
	int cx2 = ceil((x + w) / cellSize);
	int cy2 = ceil((y + h) / cellSize);
	int cz2 = ceil((z + d) / cellSize);
	cw = cx2 - cx + 1;
	ch = cy2 - cy + 1;
	cd = cz2 - cz + 1;
}

struct World;
/*------------------------------------------
 -- Responses
 ------------------------------------------*/
struct Response {
	virtual void ComputeResponse(World *world, Collision &col, double x,
			double y, double w, double h, double goalX, double goalY,
			ColFilter *filter, double &actualX, double &actualY,std::vector<Collision> &cols)=0;
	virtual void ComputeResponse3(World *world, Collision &col, double x,
			double y, double z, double w, double h, double d, double goalX, double goalY, double goalZ,
			ColFilter *filter, double &actualX, double &actualY, double &actualZ, std::vector<Collision> &cols)=0;
	virtual ~Response() {
	}
	;
};

/*------------------------------------------
 -- World
 ------------------------------------------*/

struct Cell {
	std::set<int> items;
	int x, y;
	Cell() :
			x(0), y(0) {
	}
};

struct Cell3 {
	std::set<int> items;
	int x, y, z;
	Cell3() :
			x(0), y(0), z(0) {
	}
};

struct ItemInfo {
	int item;
	double ti1, ti2, weight;
	double x1, y1, z1, x2, y2, z2;
};

struct ItemFilter {
	virtual bool Filter(int item)=0;
	virtual ~ItemFilter() {
	}
	;
};

struct World {
	int cellSize;
	int itemId=0;
    double precision=0;
	bool d3=false;
	std::map<int, Rect> rects;
	std::map<int, std::map<int, Cell> > rows;
	std::map<int, std::map<int, std::map<int, Cell3> > > rows3;
	std::map<std::string, Response *> responses;
//-- Private functions and methods
	static bool sortByWeight(ItemInfo a, ItemInfo b) {
		return a.weight < b.weight;
	}

	static bool sortByTiAndDistance(Collision a, Collision b) {
		if (a.ti == b.ti)
			return a.distance < b.distance;
		return a.ti < b.ti;
	}

	void addItemToCell(int item, int cx, int cy) {
		rows[cy][cx].items.insert(item);
	}
	void addItemToCell3(int item, int cx, int cy, int cz) {
		rows3[cz][cy][cx].items.insert(item);
	}

	bool removeItemFromCell(int item, int cx, int cy) {
		std::map<int, std::map<int, Cell> >::iterator row = rows.find(cy);
		if (row == rows.end())
			return false;
		std::map<int, Cell>::iterator cell = row->second.find(cx);
		if (cell == row->second.end())
			return false;
		if (cell->second.items.find(item) == cell->second.items.end())
			return false;
		cell->second.items.erase(item);
		return true;
	}
	bool removeItemFromCell3(int item, int cx, int cy,int cz) {
		std::map<int, std::map<int, std::map<int, Cell3> > >::iterator row3 = rows3.find(cz);
		if (row3 == rows3.end())
			return false;
		std::map<int, std::map<int, Cell3> >::iterator row = row3->second.find(cy);
		if (row == row3->second.end())
			return false;
		std::map<int, Cell3>::iterator cell = row->second.find(cx);
		if (cell == row->second.end())
			return false;
		if (cell->second.items.find(item) == cell->second.items.end())
			return false;
		cell->second.items.erase(item);
		return true;
	}

	void getDictItemsInCellRect(int cl, int ct, int cw, int ch, std::set<int> &items_dict) {
		for (int cy = ct; cy < ct + ch; cy++) {
			std::map<int, std::map<int, Cell> >::iterator row = rows.find(cy);
			if (row == rows.end())
				continue;
			for (int cx = cl; cx < cl + cw; cx++) {
				std::map<int, Cell>::iterator cell = row->second.find(cx);
				if (cell == row->second.end())
					continue;
				if (cell->second.items.size() > 0) {
					for (std::set<int>::iterator it =
							cell->second.items.begin();
							it != cell->second.items.end(); it++)
						items_dict.insert(*it);
				}
			}
		}
	}
	void getDictItemsInCellCube(int cl, int ct, int cf, int cw, int ch, int cd, std::set<int> &items_dict) {
		for (int cz = cf; cz < cf + cd; cz++) {
			std::map<int, std::map<int, std::map<int, Cell3> > >::iterator row3 = rows3.find(cz);
			if (row3 == rows3.end())
				continue;
			for (int cy = ct; cy < ct + ch; cy++) {
				std::map<int, std::map<int, Cell3> >::iterator row = row3->second.find(cy);
				if (row == row3->second.end())
					continue;
				for (int cx = cl; cx < cl + cw; cx++) {
					std::map<int, Cell3>::iterator cell = row->second.find(cx);
					if (cell == row->second.end())
						continue;
					if (cell->second.items.size() > 0) {
						for (std::set<int>::iterator it =
								cell->second.items.begin();
								it != cell->second.items.end(); it++)
							items_dict.insert(*it);
					}
				}
			}
		}
	}
	struct _CellTraversal {
		World *world;
		std::set<Cell*> cells;
	};
	struct _CellTraversal3 {
		World *world;
		std::set<Cell3*> cells;
	};
	static void cellsTraversal_(void *ctx, int cx, int cy) {
		struct _CellTraversal *ct = (struct _CellTraversal *) ctx;
		std::map<int, std::map<int, Cell> >::iterator row = ct->world->rows.find(
				cy);
		if (row == ct->world->rows.end())
			return;
		std::map<int, Cell>::iterator cell = row->second.find(cx);
		if (cell == row->second.end())
			return;
		ct->cells.insert(&cell->second);
	}
	static void cellsTraversal3_(void *ctx, int cx, int cy,int cz) {
		struct _CellTraversal3 *ct = (struct _CellTraversal3 *) ctx;
		std::map<int, std::map<int, std::map<int, Cell3> > >::iterator row3 = ct->world->rows3.find(cz);
		if (row3 == ct->world->rows3.end())
			return;
		std::map<int, std::map<int, Cell3> >::iterator row = row3->second.find(cy);
		if (row == row3->second.end())
			return;
		std::map<int, Cell3>::iterator cell = row->second.find(cx);
		if (cell == row->second.end())
			return;
		ct->cells.insert(&cell->second);
	}
	std::set<Cell*> getCellsTouchedBySegment(double x1, double y1, double x2,
			double y2) {
		struct _CellTraversal ct;
		ct.world = this;
		grid_traverse(cellSize, x1, y1, x2, y2, cellsTraversal_, &ct);
		return ct.cells;
	}

	std::set<Cell3*> getCellsTouchedBySegment3(double x1, double y1, double z1, double x2,
			double y2, double z2) {
		struct _CellTraversal3 ct;
		ct.world = this;
		grid_traverse3(cellSize, x1, y1, z1, x2, y2, z2, cellsTraversal3_, &ct);
		return ct.cells;
	}

	void getInfoAboutItemsTouchedBySegment(double x1,
			double y1, double x2, double y2, ItemFilter *filter, std::vector<ItemInfo> &itemInfo) {
		std::set<Cell *> cells = getCellsTouchedBySegment(x1, y1, x2, y2);
		std::set<int> visited;

		for (std::set<Cell *>::iterator it = cells.begin(); it != cells.end();
				it++) {
			Cell *cell = (*it);
			for (std::set<int>::iterator i = cell->items.begin();
					i != cell->items.end(); i++) {
                if (visited.find(*i) == visited.end()) {
					visited.insert(*i);
					if ((!filter) || filter->Filter(*i)) {
						Rect r = rects[*i];
						double nx1, ny1, nx2, ny2;
						double ti1 = 0;
						double ti2 = 1;
						rect_getSegmentIntersectionIndices(r.x, r.y, r.w, r.h,
								x1, y1, x2, y2, ti1, ti2, nx1, ny1, nx2, ny2);
						if (ti1
								&& (((0 < ti1) && (ti1 < 1))
										|| ((0 < ti2) && (ti2 < 1)))) {
							//-- the sorting is according to the t of an infinite line, not the segment
							double tii0 = -MATH_HUGE;
							double tii1 = MATH_HUGE;
							rect_getSegmentIntersectionIndices(r.x, r.y, r.w,
									r.h, x1, y1, x2, y2, tii0, tii1, nx1, ny1,
									nx2, ny2);
							ItemInfo ii;
							ii.item = *i;
							ii.ti1 = ti1;
							ii.ti2 = ti2;
							ii.weight = tii0 < tii1 ? tii0 : tii1;
							itemInfo.push_back(ii);
						}
					}
				}
			}
		}
		std::sort(itemInfo.begin(), itemInfo.end(), sortByWeight);
	}

	void getInfoAboutItemsTouchedBySegment3(double x1,
			double y1, double z1, double x2, double y2, double z2, ItemFilter *filter, std::vector<ItemInfo> &itemInfo) {
		std::set<Cell3 *> cells = getCellsTouchedBySegment3(x1, y1, z1, x2, y2, z2);
		std::set<int> visited;

		for (std::set<Cell3 *>::iterator it = cells.begin(); it != cells.end();
				it++) {
			Cell3 *cell = (*it);
			for (std::set<int>::iterator i = cell->items.begin();
					i != cell->items.end(); i++) {
                if (visited.find(*i) == visited.end()) {
					visited.insert(*i);
					if ((!filter) || filter->Filter(*i)) {
						Rect r = rects[*i];
						double nx1, ny1, nz1, nx2, ny2, nz2;
						double ti1 = 0;
						double ti2 = 1;
						cube_getSegmentIntersectionIndices(r.x, r.y, r.z, r.w, r.h, r.d,
								x1, y1, z1, x2, y2, z2, ti1, ti2, nx1, ny1, nz1, nx2, ny2, nz2);
						if (ti1
								&& (((0 < ti1) && (ti1 < 1))
										|| ((0 < ti2) && (ti2 < 1)))) {
							//-- the sorting is according to the t of an infinite line, not the segment
							double tii0 = -MATH_HUGE;
							double tii1 = MATH_HUGE;
							cube_getSegmentIntersectionIndices(r.x, r.y, r.z, r.w,
									r.h, r.d, x1, y1, z1, x2, y2, z2, tii0, tii1, nx1, ny1, nz1,
									nx2, ny2, nz2);
							ItemInfo ii;
							ii.item = *i;
							ii.ti1 = ti1;
							ii.ti2 = ti2;
							ii.weight = tii0 < tii1 ? tii0 : tii1;
							itemInfo.push_back(ii);
						}
					}
				}
			}
		}
		std::sort(itemInfo.begin(), itemInfo.end(), sortByWeight);
	}

	Response *getResponseByName(const char *name) {
		Response *response = responses[name];
		if (!response) {
			// TODO error(('Unknown collision type: %s (%s)'):format(name, type(name)))
			response = responses["slide"];
		}
		return response;
	}

//-- Misc Public Methods
	void addResponse(const char *name, Response *response) {
		responses[name] = response;
	}

	void project(int item, double x, double y, double w,
			double h, double goalX, double goalY, ColFilter *filter,std::vector<Collision> &collisions) {
		//assertIsRect(x,y,w,h) TODO

		//goalX = goalX or x
		//goalY = goalY or y
		//filter  = filter  or defaultFilter

		std::set<int> visited;
		if (item)
			visited.insert(item);

		//-- This could probably be done with less cells using a polygon raster over the cells instead of a
		//-- bounding rect of the whole movement. Conditional to building a queryPolygon method
		double tl = (goalX < x) ? goalX : x;
		double tt = (goalY < y) ? goalY : y;
		double tr = ((goalX + w) > (x + w)) ? goalX + w : x + w;
		double tb = ((goalY + h) > (y + h)) ? goalY + h : y + h;
		double tw = tr - tl;
		double th = tb - tt;

		int cl, ct, cw, ch;
		grid_toCellRect(cellSize, tl, tt, tw, th, cl, ct, cw, ch);

		std::set<int> dictItemsInCellRect;
		getDictItemsInCellRect(cl, ct, cw, ch,dictItemsInCellRect);

		for (std::set<int>::iterator it = dictItemsInCellRect.begin();
				it != dictItemsInCellRect.end(); it++) {
			int other = *it;
			if (visited.find(other) == visited.end()) {
				visited.insert(other);
                const char *responseName = filter?(filter->Filter(item, other)):"slide";
                if (responseName) {
					double ox, oy, ow, oh;
					getRect(other, ox, oy, ow, oh);
					Collision col;
					if (rect_detectCollision(x, y, w, h, ox, oy, ow, oh, goalX,
							goalY, col)) {
						col.other = other;
						col.item = item;
						col.type = responseName;
                        alignPoint(col.touch.x,col.touch.y);
                        collisions.push_back(col);
					}
				}
			}
		}

		std::sort(collisions.begin(), collisions.end(), sortByTiAndDistance);
	}

	void project3(int item, double x, double y, double z, double w,
			double h, double d, double goalX, double goalY, double goalZ, ColFilter *filter,std::vector<Collision> &collisions) {
		//assertIsRect(x,y,w,h) TODO

		//goalX = goalX or x
		//goalY = goalY or y
		//filter  = filter  or defaultFilter

		std::set<int> visited;
		if (item)
			visited.insert(item);

		//-- This could probably be done with less cells using a polygon raster over the cells instead of a
		//-- bounding rect of the whole movement. Conditional to building a queryPolygon method
		double tl = (goalX < x) ? goalX : x;
		double tt = (goalY < y) ? goalY : y;
		double tf = (goalZ < z) ? goalZ : z;
		double tr = ((goalX + w) > (x + w)) ? goalX + w : x + w;
		double tb = ((goalY + h) > (y + h)) ? goalY + h : y + h;
		double tk = ((goalZ + d) > (z + d)) ? goalZ + d : z + d;
		double tw = tr - tl;
		double th = tb - tt;
		double td = tk - tf;

		int cl, ct, cf, cw, ch, cd;
		grid_toCellCube(cellSize, tl, tt, tf, tw, th, td, cl, ct, cf, cw, ch, cd);

		std::set<int> dictItemsInCellRect;
		getDictItemsInCellCube(cl, ct, cf, cw, ch, cd, dictItemsInCellRect);

		for (std::set<int>::iterator it = dictItemsInCellRect.begin();
				it != dictItemsInCellRect.end(); it++) {
			int other = *it;
			if (visited.find(other) == visited.end()) {
				visited.insert(other);
                const char *responseName = filter?(filter->Filter(item, other)):"slide";
				if (responseName) {
					double ox, oy, oz, ow, oh, od;
					getCube(other, ox, oy, oz, ow, oh, od);
					Collision col;
					if (cube_detectCollision(x, y, z, w, h, d, ox, oy, oz, ow, oh, od, goalX,
							goalY, goalZ, col)) {
						col.other = other;
						col.item = item;
						col.type = responseName;
                        alignPoint3(col.touch.x,col.touch.y,col.touch.z);
                        collisions.push_back(col);
					}
				}
			}
		}

		std::sort(collisions.begin(), collisions.end(), sortByTiAndDistance);
	}

	int countCells() {
		int count = 0;
		if (d3)
		{
			for (std::map<int, std::map<int, std::map<int,Cell3> > >::iterator row3 = rows3.begin();
					row3 != rows3.end(); row3++)
				for (std::map<int, std::map<int, Cell3> >::iterator row = row3->second.begin();
						row != row3->second.end(); row++)
					count += row->second.size();
		}
		else
		{
			for (std::map<int, std::map<int, Cell> >::iterator row = rows.begin();
					row != rows.end(); row++)
				count += row->second.size();
		}
		return count;
	}

	bool hasItem(int item) {
		return rects.find(item) != rects.end();
	}

	std::set<int> getItems() {
		std::set<int> items;
		for (std::map<int, Rect>::iterator r = rects.begin(); r != rects.end();
				r++)
			items.insert(r->first);
		return items;
	}

	int countItems() {
		return rects.size();
	}

	void getRect(int item, double &x, double &y, double &w, double &h) {
		Rect r = rects[item];
		x = r.x;
		y = r.y;
		w = r.w;
		h = r.h;
	}
	void getCube(int item, double &x, double &y, double &z, double &w, double &h, double &d) {
		Rect r = rects[item];
		x = r.x;
		y = r.y;
		z = r.z;
		w = r.w;
		h = r.h;
		d = r.d;
	}


	void toWorld(int cx, int cy, double &x, double &y) {
		grid_toWorld(cellSize, cx, cy, x, y);
	}
	void toCell(double x, double y, int &cx, int &cy) {
		grid_toCell(cellSize, x, y, cx, cy);
	}
	void toWorld3(int cx, int cy, int cz, double &x, double &y, double &z) {
		grid_toWorld3(cellSize, cx, cy, cz, x, y, z);
	}
	void toCell3(double x, double y, double z, int &cx, int &cy, int &cz) {
		grid_toCell3(cellSize, x, y, z, cx, cy, cz);
	}

//--- Query methods

	void queryRect(double x, double y, double w, double h,
			ItemFilter *filter, std::set<int> &dictItemsInCellRect) {

		int cl, ct, cw, ch;
		grid_toCellRect(cellSize, x, y, w, h, cl, ct, cw, ch);
		getDictItemsInCellRect(cl, ct, cw,
				ch, dictItemsInCellRect);
		for (std::set<int>::iterator it = dictItemsInCellRect.begin();
				it != dictItemsInCellRect.end();) {
			bool drop=(filter && !filter->Filter(*it));
			if (!drop)
			{
				Rect rect = rects[*it];
				drop|=!rect_isIntersecting(x, y, w, h, rect.x, rect.y, rect.w,
						rect.h);
			}
			if (drop)
				dictItemsInCellRect.erase(it++);
			else
				++it;
		}
	}
	void queryCube(double x, double y, double z, double w, double h,double d,
			ItemFilter *filter, std::set<int> &dictItemsInCellRect) {

		int cl, ct, cf, cw, ch, cd;
		grid_toCellCube(cellSize, x, y, z, w, h, d, cl, ct, cf, cw, ch, cd);
		getDictItemsInCellCube(cl, ct, cf, cw,
				ch, cd, dictItemsInCellRect);
		for (std::set<int>::iterator it = dictItemsInCellRect.begin();
				it != dictItemsInCellRect.end();) {
			bool drop=(filter && !filter->Filter(*it));
			if (!drop)
			{
				Rect rect = rects[*it];
				drop|=!cube_isIntersecting(x, y, z, w, h, d, rect.x, rect.y, rect.z, rect.w,
						rect.h, rect.d);
			}
			if (drop)
				dictItemsInCellRect.erase(it++);
			else
				++it;
		}
	}

	void queryPoint(double x, double y, ItemFilter *filter, std::set<int> &dictItemsInCellRect) {
		int cx, cy;
		toCell(x, y, cx, cy);
		getDictItemsInCellRect(cx, cy, 1,
				1,dictItemsInCellRect);
		for (std::set<int>::iterator it = dictItemsInCellRect.begin();
				it != dictItemsInCellRect.end();) {
			Rect rect = rects[*it];
			if ((filter && !filter->Filter(*it))
					|| !rect_containsPoint(rect.x, rect.y, rect.w, rect.h, x,
							y))
				dictItemsInCellRect.erase(it++);
			else
				++it;
		}
	}

	void queryPoint3(double x, double y, double z, ItemFilter *filter, std::set<int> &dictItemsInCellRect) {
		int cx, cy, cz;
		toCell3(x, y, z, cx, cy, cz);
		getDictItemsInCellCube(cx, cy, cz, 1,
				1,1,dictItemsInCellRect);
		for (std::set<int>::iterator it = dictItemsInCellRect.begin();
				it != dictItemsInCellRect.end();) {
			Rect rect = rects[*it];
			if ((filter && !filter->Filter(*it))
					|| !cube_containsPoint(rect.x, rect.y, rect.z, rect.w, rect.h, rect.d, x,
							y, z))
				dictItemsInCellRect.erase(it++);
			else
				++it;
		}
	}

	void querySegment(double x1, double y1, double x2, double y2,
			ItemFilter *filter, std::set<int> &items) {
		std::vector<ItemInfo> itemInfo;
		getInfoAboutItemsTouchedBySegment(x1, y1,
				x2, y2, filter, itemInfo);
		for (std::vector<ItemInfo>::iterator it = itemInfo.begin();
				it != itemInfo.end(); it++)
			items.insert((*it).item);
	}
	void querySegment3(double x1, double y1, double z1, double x2, double y2, double z2,
			ItemFilter *filter, std::set<int> &items) {
		std::vector<ItemInfo> itemInfo;
		getInfoAboutItemsTouchedBySegment3(x1, y1, z1,
				x2, y2, z2, filter, itemInfo);
		for (std::vector<ItemInfo>::iterator it = itemInfo.begin();
				it != itemInfo.end(); it++)
			items.insert((*it).item);
	}

	void querySegmentWithCoords(double x1, double y1, double x2,
			double y2, ItemFilter *filter, std::vector<ItemInfo> &itemInfo2) {
		std::vector<ItemInfo> itemInfo;
		getInfoAboutItemsTouchedBySegment(x1, y1,
				x2, y2, filter, itemInfo);
		double dx = x2 - x1, dy = y2 - y1;
		for (std::vector<ItemInfo>::iterator it = itemInfo.begin();
				it != itemInfo.end(); it++) {
			ItemInfo i=*it;
			i.x1 = x1 + dx * i.ti1;
			i.y1 = y1 + dy * i.ti1;
			i.x2 = x1 + dx * i.ti2;
			i.y2 = y1 + dy * i.ti2;
			itemInfo2.push_back(i);
		}
	}
	void querySegmentWithCoords3(double x1, double y1, double z1, double x2,
			double y2, double z2, ItemFilter *filter, std::vector<ItemInfo> &itemInfo2) {
		std::vector<ItemInfo> itemInfo;
		getInfoAboutItemsTouchedBySegment3(x1, y1, z1,
				x2, y2, z2, filter, itemInfo);
		double dx = x2 - x1, dy = y2 - y1, dz = z2 - z1;
		for (std::vector<ItemInfo>::iterator it = itemInfo.begin();
				it != itemInfo.end(); it++) {
			ItemInfo i=*it;
			i.x1 = x1 + dx * i.ti1;
			i.y1 = y1 + dy * i.ti1;
			i.z1 = z1 + dz * i.ti1;
			i.x2 = x1 + dx * i.ti2;
			i.y2 = y1 + dy * i.ti2;
			i.z2 = z1 + dz * i.ti2;
			itemInfo2.push_back(i);
		}
	}

//--- Main methods
	int allocateId() {
		int nid=(++itemId);
		while (rects.find(nid)!=rects.end())
			nid++;
		itemId=nid;
		return nid;
	}

#define ALIGNR(v) v=round(v/precision)*precision;
    void alignRect(Rect &r) {
        if (!precision) return;
        ALIGNR(r.x);
        ALIGNR(r.y);
        ALIGNR(r.z);
        ALIGNR(r.w);
        ALIGNR(r.h);
        ALIGNR(r.d);
    }
    void alignPoint(double &x,double &y) {
        if (!precision) return;
        ALIGNR(x);
        ALIGNR(y);
    }
    void alignPoint3(double &x,double &y, double &z) {
        if (!precision) return;
        ALIGNR(x);
        ALIGNR(y);
        ALIGNR(z);
    }
#undef ALIGNR

	void add(int item, double x, double y, double w, double h) {
		Rect r;
		r.x = x;
		r.y = y;
        r.z = 0;
		r.w = w;
		r.h = h;
        r.d = 0;
        alignRect(r);
		rects[item] = r;
		int cl, ct, cw, ch;

		grid_toCellRect(cellSize, x, y, w, h, cl, ct, cw, ch);
		for (int cy = ct; cy < ct + ch; cy++)
			for (int cx = cl; cx < cl + cw; cx++)
				addItemToCell(item, cx, cy);
	}
	void add3(int item, double x, double y, double z, double w, double h, double d) {
		Rect r;
		r.x = x;
		r.y = y;
		r.z = z;
		r.w = w;
		r.h = h;
		r.d = d;
        alignRect(r);
        rects[item] = r;
		int cl, ct, cf, cw, ch, cd;

		grid_toCellCube(cellSize, x, y, z, w, h, d, cl, ct, cf, cw, ch, cd);
		for (int cz = cf; cz < cf + cd; cz++)
			for (int cy = ct; cy < ct + ch; cy++)
				for (int cx = cl; cx < cl + cw; cx++)
					addItemToCell3(item, cx, cy, cz);
	}

	void remove(int item) {
		Rect r = rects[item];
		int cl, ct, cf, cw, ch, cd;
		if (d3) {
			grid_toCellCube(cellSize, r.x, r.y, r.z, r.w, r.h, r.d, cl, ct, cf, cw, ch, cd);
			for (int cz = cf; cz < cf + cd; cz++)
				for (int cy = ct; cy < ct + ch; cy++)
					for (int cx = cl; cx < cl + cw; cx++)
						removeItemFromCell3(item, cx, cy, cz);
		}
		else {
			grid_toCellRect(cellSize, r.x, r.y, r.w, r.h, cl, ct, cw, ch);
			for (int cy = ct; cy < ct + ch; cy++)
				for (int cx = cl; cx < cl + cw; cx++)
					removeItemFromCell(item, cx, cy);
		}
		rects.erase(item);
	}

	void update(int item, double x2, double y2, double w2, double h2) {
		Rect r = rects[item];
		if (w2 <= 0)
			w2 = r.w;
		if (h2 <= 0)
			h2 = r.h;

		if ((r.x != x2) || (r.y != y2) || (r.w != w2) || (r.h != h2)) {
			int cl1, ct1, cw1, ch1;
			grid_toCellRect(cellSize, r.x, r.y, r.w, r.h, cl1, ct1, cw1, ch1);
			int cl2, ct2, cw2, ch2;
			grid_toCellRect(cellSize, x2, y2, w2, h2, cl2, ct2, cw2, ch2);

			if ((cl1 != cl2) || (ct1 != ct2) || (cw1 != cw2) || (ch1 != ch2)) {

				int cr1 = cl1 + cw1 - 1, cb1 = ct1 + ch1 - 1;
				int cr2 = cl2 + cw2 - 1, cb2 = ct2 + ch2 - 1;
				bool cyOut;

				for (int cy = ct1; cy <= cb1; cy++) {
					cyOut = (cy < ct2) || (cy > cb2);
					for (int cx = cl1; cx <= cr1; cx++) {
						if (cyOut || (cx < cl2) || (cx > cr2))
							removeItemFromCell(item, cx, cy);
					}
				}

				for (int cy = ct2; cy <= cb2; cy++) {
					cyOut = (cy < ct1) || (cy > cb1);
					for (int cx = cl2; cx <= cr2; cx++) {
						if (cyOut || (cx < cl1) || (cx > cr1))
							addItemToCell(item, cx, cy);
					}
				}
			}

			Rect r;
			r.x = x2;
			r.y = y2;
            r.z = 0;
            r.w = w2;
			r.h = h2;
            r.d = 0;
            alignRect(r);
            rects[item] = r;
		}
	}
	void update3(int item, double x2, double y2, double z2, double w2, double h2, double d2) {
		Rect r = rects[item];
		if (w2 <= 0)
			w2 = r.w;
		if (h2 <= 0)
			h2 = r.h;
		if (d2 <= 0)
			d2 = r.d;

		if ((r.x != x2) || (r.y != y2) || (r.z != z2) || (r.w != w2) || (r.h != h2) || (r.d != d2)) {
			int cl1, ct1, cf1, cw1, ch1, cd1;
			grid_toCellCube(cellSize, r.x, r.y, r.z, r.w, r.h, r.d, cl1, ct1, cf1, cw1, ch1, cd1);
			int cl2, ct2, cf2, cw2, ch2, cd2;
			grid_toCellCube(cellSize, x2, y2, z2, w2, h2, d2, cl2, ct2, cf2, cw2, ch2, cd2);

			if ((cl1 != cl2) || (ct1 != ct2)  || (cf1 != cf2) || (cw1 != cw2) || (ch1 != ch2) || (cd1 != cd2)) {

				int cr1 = cl1 + cw1 - 1, cb1 = ct1 + ch1 - 1, ck1 = cf1 + cd1 - 1;
				int cr2 = cl2 + cw2 - 1, cb2 = ct2 + ch2 - 1, ck2 = cf2 + cd2 - 1;
				bool cyOut, czOut;

				for (int cz = cf1; cz <= ck1; cz++) {
					czOut = (cz < cf2) || (cz > ck2);
					for (int cy = ct1; cy <= cb1; cy++) {
						cyOut = (cy < ct2) || (cy > cb2);
						for (int cx = cl1; cx <= cr1; cx++) {
							if (czOut || cyOut || (cx < cl2) || (cx > cr2))
								removeItemFromCell3(item, cx, cy, cz);
						}
					}
				}

				for (int cz = cf2; cz <= ck2; cz++) {
					czOut = (cz < cf1) || (cz > ck1);
					for (int cy = ct2; cy <= cb2; cy++) {
						cyOut = (cy < ct1) || (cy > cb1);
						for (int cx = cl2; cx <= cr2; cx++) {
							if (czOut || cyOut || (cx < cl1) || (cx > cr1))
								addItemToCell3(item, cx, cy, cz);
						}
					}
				}
			}

			Rect r;
			r.x = x2;
			r.y = y2;
			r.z = z2;
			r.w = w2;
			r.h = h2;
			r.d = d2;
            alignRect(r);
            rects[item] = r;
		}
	}

	void move(int item, double goalX, double goalY,
			ColFilter *filter, double &actualX, double &actualY,std::vector<Collision> &cols) {
		check(item, goalX, goalY, filter, actualX,
				actualY,cols);
		update(item, actualX, actualY, -1, -1);
	}

	void move3(int item, double goalX, double goalY, double goalZ,
			ColFilter *filter, double &actualX, double &actualY, double &actualZ, std::vector<Collision> &cols) {
		check3(item, goalX, goalY, goalZ, filter, actualX,
				actualY,actualZ,cols);
		update3(item, actualX, actualY, actualZ, -1, -1, -1);
	}

	struct VisitedFilter: ColFilter {
		std::set<int> visited;
		ColFilter *filter;
		const char *Filter(int item, int other) {
			if (visited.find(other) != visited.end())
				return NULL;
            return filter?filter->Filter(item, other):"slide";
		}
	};
	void check(int item, double goalX, double goalY,
			ColFilter *filter, double &actualX, double &actualY,std::vector<Collision> &cols) {
		defaultFilter df;
		if (!filter)
			filter = &df;

		VisitedFilter vf;
		vf.visited.insert(item);
		vf.filter = filter;

		Rect r = rects[item];

		std::vector<Collision> projected_cols;
		project(item, r.x, r.y, r.w,
				r.h, goalX, goalY, &vf,projected_cols);

		while (projected_cols.size() > 0) {
			Collision col = projected_cols[0];
			vf.visited.insert(col.other);
			Response *response = getResponseByName(col.type);

			projected_cols.clear();
			response->ComputeResponse(this, col, r.x, r.y, r.w, r.h,
					goalX, goalY, &vf, goalX, goalY,projected_cols);
            alignPoint(goalX,goalY);
            cols.push_back(col);
		}

		actualX = goalX;
		actualY = goalY;
    }
	void check3(int item, double goalX, double goalY, double goalZ,
			ColFilter *filter, double &actualX, double &actualY,double &actualZ,std::vector<Collision> &cols) {
		defaultFilter df;
		if (!filter)
			filter = &df;

		VisitedFilter vf;
		vf.visited.insert(item);
		vf.filter = filter;

		Rect r = rects[item];

		std::vector<Collision> projected_cols;
		project3(item, r.x, r.y, r.z, r.w,
				r.h, r.d, goalX, goalY, goalZ, &vf,projected_cols);

		while (projected_cols.size() > 0) {
			Collision col = projected_cols[0];
			vf.visited.insert(col.other);
			Response *response = getResponseByName(col.type);

			projected_cols.clear();
			response->ComputeResponse3(this, col, r.x, r.y, r.z, r.w, r.h, r.d,
					goalX, goalY, goalZ, &vf, goalX, goalY,goalZ, projected_cols);
            cols.push_back(col);
		}

		actualX = goalX;
		actualY = goalY;
		actualZ = goalZ;
    }
};

struct TouchResponse: Response {
	void ComputeResponse(World *world, Collision &col, double x,
			double y, double w, double h, double goalX, double goalY,
			ColFilter *filter, double &actualX, double &actualY,std::vector<Collision> &cols) {
		UNUSED(world); UNUSED(x); UNUSED(y); UNUSED(w); UNUSED(h);
		UNUSED(filter); UNUSED(goalX); UNUSED(goalY); UNUSED(cols);
		actualX = col.touch.x;
		actualY = col.touch.y;
	}
	void ComputeResponse3(World *world, Collision &col, double x, double y, double z,
			double w, double h, double d, double goalX, double goalY, double goalZ,
			ColFilter *filter, double &actualX, double &actualY, double &actualZ,
			std::vector<Collision> &cols) {
		UNUSED(world); UNUSED(x); UNUSED(y); UNUSED(z); UNUSED(w); UNUSED(h); UNUSED(d);
		UNUSED(filter); UNUSED(goalX); UNUSED(goalY); UNUSED(goalZ); UNUSED(cols);
		actualX = col.touch.x;
		actualY = col.touch.y;
		actualZ = col.touch.z;
	}
};

struct CrossResponse: Response {
	void ComputeResponse(World *world, Collision &col, double x,
			double y, double w, double h, double goalX, double goalY,
			ColFilter *filter, double &actualX, double &actualY,std::vector<Collision> &cols) {
		world->project(col.item, x, y, w, h, goalX,
				goalY, filter,cols);
		actualX = goalX;
		actualY = goalY;
	}
	void ComputeResponse3(World *world, Collision &col, double x, double y, double z,
			double w, double h, double d, double goalX, double goalY, double goalZ,
			ColFilter *filter, double &actualX, double &actualY, double &actualZ,
			std::vector<Collision> &cols) {

		world->project3(col.item, x, y, z, w, h, d, goalX,
				goalY, goalZ, filter,cols);
		actualX = goalX;
		actualY = goalY;
		actualZ = goalZ;
	}
};

struct SlideResponse: Response {
	void ComputeResponse(World *world, Collision &col, double x,
			double y, double w, double h, double goalX, double goalY,
			ColFilter *filter, double &actualX, double &actualY,std::vector<Collision> &cols) {
		//goalX = goalX or x TODO
		//goalY = goalY or y TODO

		double sx = col.touch.x;
		double sy = col.touch.y;

		if ((col.move.x != 0) || (col.move.y != 0)) {
			if (col.normal.x == 0)
				sx = goalX;
			else
				sy = goalY;
		}

		col.response.x = sx;
		col.response.y = sy;

		x = col.touch.x;
		y = col.touch.y;
		goalX = sx;
		goalY = sy;
		world->project(col.item, x, y, w, h, goalX,
				goalY, filter,cols);
		actualX = goalX;
		actualY = goalY;
	}
	void ComputeResponse3(World *world, Collision &col, double x, double y, double z,
			double w, double h, double d, double goalX, double goalY, double goalZ,
			ColFilter *filter, double &actualX, double &actualY, double &actualZ,
			std::vector<Collision> &cols) {
		//goalX = goalX or x TODO
		//goalY = goalY or y TODO
		//goalZ = goalZ or z TODO

		double sx = col.touch.x;
		double sy = col.touch.y;
		double sz = col.touch.z;

		if ((col.move.x != 0) || (col.move.y != 0) || (col.move.z != 0)) {
			//If normal is 0, then slide along the corresponding axis
			if (col.normal.x == 0)
				sx = goalX;
			if (col.normal.y == 0)
				sy = goalY;
			if (col.normal.z == 0)
                sz = goalZ;
		}

		col.response.x = sx;
		col.response.y = sy;
		col.response.z = sz;

		x = col.touch.x;
		y = col.touch.y;
		z = col.touch.z;
		goalX = sx;
		goalY = sy;
		goalZ = sz;
		world->project3(col.item, x, y, z, w, h, d, goalX,
				goalY, goalZ, filter,cols);
		actualX = goalX;
		actualY = goalY;
		actualZ = goalZ;
	}
};

struct BounceResponse: Response {
	void ComputeResponse(World *world, Collision &col, double x,
			double y, double w, double h, double goalX, double goalY,
			ColFilter *filter, double &actualX, double &actualY,std::vector<Collision> &cols) {
		double tx = col.touch.x;
		double ty = col.touch.y;
		double bx = tx;
		double by = ty;

		if ((col.move.x != 0) || (col.move.y != 0)) {
			double bnx = goalX - tx, bny = goalY - ty;
			if (col.normal.x == 0)
				bny = -bny;
			else
				bnx = -bnx;
			bx = tx + bnx;
			by = ty + bny;
		}

		col.response.x = bx;
		col.response.y = by;
		x = tx;
		y = ty;
		goalX = bx;
		goalY = by;
		world->project(col.item, x, y, w, h, goalX,
				goalY, filter, cols);
		actualX = goalX;
		actualY = goalY;
	}
	void ComputeResponse3(World *world, Collision &col, double x, double y, double z,
			double w, double h, double d, double goalX, double goalY, double goalZ,
			ColFilter *filter, double &actualX, double &actualY, double &actualZ,
			std::vector<Collision> &cols) {
		double tx = col.touch.x;
		double ty = col.touch.y;
		double tz = col.touch.y;
		double bx = tx;
		double by = ty;
		double bz = tz;

		if ((col.move.x != 0) || (col.move.y != 0) || (col.move.z != 0)) {
			double bnx = goalX - tx, bny = goalY - ty, bnz = goalZ - tz;
			//If normal is not 0, then bounce along the corresponding axis
			if (col.normal.x != 0)
				bnx = -bnx;
			if (col.normal.y != 0)
				bny = -bny;
			if (col.normal.z != 0)
				bnz = -bnz;
			bx = tx + bnx;
			by = ty + bny;
			bz = tz + bnz;
		}

		col.response.x = bx;
		col.response.y = by;
		col.response.z = bz;
		x = tx;
		y = ty;
		z = tz;
		goalX = bx;
		goalY = by;
		goalZ = bz;
		world->project3(col.item, x, y, z, w, h, d, goalX,
				goalY, goalZ, filter,cols);
		actualX = goalX;
		actualY = goalY;
		actualZ = goalZ;
	}
};

static CrossResponse responseCross;
static TouchResponse responseTouch;
static SlideResponse responseSlide;
static BounceResponse responseBounce;

static int worldCreate(lua_State *L) {
	World *w = new World();
	g_pushInstance(L, "BumpWorld", w);
	lua_newtable(L);
	lua_setfield(L, -2, "__items");
	lua_newtable(L);
	lua_setfield(L, -2, "__itemsr");

	w->addResponse("touch", &responseTouch);
	w->addResponse("cross", &responseCross);
	w->addResponse("slide", &responseSlide);
	w->addResponse("bounce", &responseBounce);

	return 1;
}

static int worldDestruct(void *p) {
	World *w = (World *)GIDEROS_DTOR_UDATA(p);
	w->responses.erase("touch");
	w->responses.erase("cross");
	w->responses.erase("bounce");
	w->responses.erase("slide");
	delete w;
	return 0;
}

struct LuaColFilter: ColFilter {
	lua_State *L;
	int itemsr;
	int func;
	const char *Filter(int item, int other) {
		lua_pushvalue(L, func);
		lua_rawgeti(L, itemsr - 1, item);
		lua_rawgeti(L, itemsr - 2, other);
		lua_call(L, 2, 1);

		const char *ret = NULL;
		if (lua_toboolean(L,-1))
			ret=lua_tostring(L, -1);
		lua_pop(L, 1);
		return ret;
	}
};

struct LuaItemFilter: ItemFilter {
	lua_State *L;
	int itemsr;
	int func;
	bool Filter(int item) {
		lua_pushvalue(L, func);
		lua_rawgeti(L, itemsr - 1, item);
		lua_call(L, 1, 1);
		bool ret = lua_toboolean(L,-1);
		lua_pop(L, 1);
		return ret;
	}
};

static int worldProject(lua_State *L) {
	int nac=lua_gettop(L);
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	double x,y,z,w,h,d,gx,gy,gz;
	int funcPos=9;
	if (wr->d3) {
		x = luaL_checknumber(L, 3);
		y = luaL_checknumber(L, 4);
		z = luaL_checknumber(L, 5);
		w = luaL_checknumber(L, 6);
		h = luaL_checknumber(L, 7);
		d = luaL_checknumber(L, 8);
		gx = luaL_checknumber(L, 9);
		gy = luaL_checknumber(L, 10);
		gz = luaL_checknumber(L, 11);
		funcPos=12;
	}
	else {
		x = luaL_checknumber(L, 3);
		y = luaL_checknumber(L, 4);
		w = luaL_checknumber(L, 5);
		h = luaL_checknumber(L, 6);
		gx = luaL_checknumber(L, 7);
		gy = luaL_checknumber(L, 8);
		z=d=gz=0;
	}
	bool hasFunc=(funcPos<=nac)&&!lua_isnoneornil(L, funcPos);
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	if (lua_isnil(L, -1)) {
		lua_pushfstring(L,
				"Item %s must be added to the world before getting its rect. Use world:add(item, x,y,w,h) to add it first.",
				luaL_tostring(L, 2));
		lua_error(L);
	}
	int item = lua_tonumber(L, -1);
	lua_pop(L, 2);

	ColFilter *f = NULL;
	LuaColFilter lf;
	lf.L = L;
	lf.itemsr = -1;
	if (hasFunc) {
		luaL_checktype(L, funcPos, LUA_TFUNCTION);
		lf.func = funcPos;
		f = &lf;
	}
	lua_getfield(L, 1, "__itemsr");
	std::vector<Collision> items;
	if (wr->d3)
		wr->project3(item, x, y, z, w, h, d, gx,gy,gz, f,items);
	else
		wr->project(item, x, y, w,h, gx,gy,f,items);
	lua_pop(L, 1);
	int n = 0;
	lua_newtable(L);
	for (std::vector<Collision>::iterator it = items.begin(); it != items.end();
			it++) {
		lua_newtable(L);
		lua_rawgeti(L, -2, (*it).item);
		lua_setfield(L, -2, "item");
		lua_rawgeti(L, -2, (*it).other);
		lua_setfield(L, -2, "other");
		lua_pushstring(L, (*it).type);
		lua_setfield(L, -2, "type");
		lua_pushboolean(L, (*it).overlaps);
		lua_setfield(L, -2, "overlaps");
		lua_pushnumber(L, (*it).ti);
		lua_setfield(L, -2, "ti");

		lua_newtable(L);
		lua_pushnumber(L, (*it).move.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).move.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).move.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "move");
		lua_newtable(L);
		lua_pushnumber(L, (*it).normal.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).normal.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).normal.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "normal");
		lua_newtable(L);
		lua_pushnumber(L, (*it).touch.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).touch.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).touch.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "touch");

		lua_newtable(L);
		lua_pushnumber(L, (*it).itemRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).itemRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, (*it).itemRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, (*it).itemRect.h);
		lua_setfield(L, -2, "h");
		if (wr->d3) {
			lua_pushnumber(L, (*it).itemRect.z);
			lua_setfield(L, -2, "z");
			lua_pushnumber(L, (*it).itemRect.d);
			lua_setfield(L, -2, "d");
		}
		lua_setfield(L, -2, "itemRect");
		lua_newtable(L);
		lua_pushnumber(L, (*it).otherRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).otherRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, (*it).otherRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, (*it).otherRect.h);
		lua_setfield(L, -2, "h");
		if (wr->d3) {
			lua_pushnumber(L, (*it).otherRect.z);
			lua_setfield(L, -2, "z");
			lua_pushnumber(L, (*it).otherRect.d);
			lua_setfield(L, -2, "d");
		}
		lua_setfield(L, -2, "otherRect");

		lua_rawseti(L, -2, ++n);
	}
	lua_pushinteger(L, n);

	return 2;
}

static int worldCountCells(lua_State *L) {
	World *w = (World *) g_getInstance(L, "BumpWorld", 1);
	lua_pushnumber(L, w->countCells());
	return 1;
}

static int worldCountItems(lua_State *L) {
	World *w = (World *) g_getInstance(L, "BumpWorld", 1);
	lua_pushnumber(L,w->countItems());
	return 1;
}

static int worldHasItem(lua_State *L) {
	//World *w = (World *) g_getInstance(L, "BumpWorld", 1);
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	bool isnil = lua_isnil(L, -1);
	lua_pop(L, 2);
	lua_pushboolean(L, !isnil);
	return 1;
}

static int worldGetItems(lua_State *L) {
	World *w = (World *) g_getInstance(L, "BumpWorld", 1);
	lua_getfield(L, 1, "__itemsr");
	std::set<int> items = w->getItems();
	lua_createtable(L,items.size(),0);
	int n = 0;
	for (std::set<int>::iterator it = items.begin(); it != items.end(); it++) {
		lua_rawgeti(L, -2, *it);
		lua_rawseti(L, -2, ++n);
	}
	lua_remove(L, -2);
	lua_pushinteger(L,n);
	return 2;
}

static int worldGetRect(lua_State *L) {
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	if (lua_isnil(L, -1)) {
		lua_pushfstring(L,
				"Item %s must be added to the world before getting its rect. Use world:add(item, x,y,w,h) to add it first.",
				luaL_tostring(L, 2));
		lua_error(L);
	}
	int idx = lua_tonumber(L, -1);
	lua_pop(L, 2);
	double x, y, w, h;
	wr->getRect(idx, x, y, w, h);
	lua_pushnumber(L, x);
	lua_pushnumber(L, y);
	lua_pushnumber(L, w);
	lua_pushnumber(L, h);
	return 4;
}

static int worldGetCube(lua_State *L) {
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	if (lua_isnil(L, -1)) {
		lua_pushfstring(L,
				"Item %s must be added to the world before getting its rect. Use world:add(item, x,y,w,h) to add it first.",
				luaL_tostring(L, 2));
		lua_error(L);
	}
	int idx = lua_tonumber(L, -1);
	lua_pop(L, 2);
	double x, y, z, w, h, d;
	wr->getCube(idx, x, y, z, w, h, d);
	lua_pushnumber(L, x);
	lua_pushnumber(L, y);
	lua_pushnumber(L, z);
	lua_pushnumber(L, w);
	lua_pushnumber(L, h);
	lua_pushnumber(L, d);
	return 6;
}

static int worldToWorld(lua_State *L) {
	World *w = (World *) g_getInstance(L, "BumpWorld", 1);
	int cx = luaL_checknumber(L, 2);
	int cy = luaL_checknumber(L, 3);
	double x, y, z;
	if (w->d3)
	{
		int cz = luaL_checknumber(L, 4);
		w->toWorld3(cx, cy, cz, x, y, z);
		lua_pushnumber(L, x);
		lua_pushnumber(L, y);
		lua_pushnumber(L, z);
		return 3;
	}
	else
	{
		w->toWorld(cx, cy, x, y);
		lua_pushnumber(L, x);
		lua_pushnumber(L, y);
		return 2;
	}
}

static int worldToCell(lua_State *L) {
	World *w = (World *) g_getInstance(L, "BumpWorld", 1);
	double x = luaL_checknumber(L, 2);
	double y = luaL_checknumber(L, 3);
	int cx, cy, cz;
	if (w->d3)
	{
		double z = luaL_checknumber(L, 4);
		w->toCell3(x, y, z, cx, cy, cz);
		lua_pushnumber(L, cx);
		lua_pushnumber(L, cy);
		lua_pushnumber(L, cz);
		return 3;
	}
	else {
		w->toCell(x, y, cx, cy);
		lua_pushnumber(L, cx);
		lua_pushnumber(L, cy);
		return 2;
	}
}

static int worldQueryRect(lua_State *L) {
	int nac= lua_gettop(L);
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	bool hasFilter=false;
	if ((6<=nac)&&!lua_isnoneornil(L, 6)) {
		luaL_checktype(L, 6, LUA_TFUNCTION);
		hasFilter=true;
	}
	assertIsRect(L, 2, 3, 4, 5);
	lua_getfield(L, 1, "__itemsr");

	double x = luaL_checknumber(L, 2);
	double y = luaL_checknumber(L, 3);
	double w = luaL_checknumber(L, 4);
	double h = luaL_checknumber(L, 5);
	ItemFilter *f = NULL;
	LuaItemFilter lf;
	lf.L = L;
	lf.itemsr = -1;
	if (hasFilter) {
		lf.func = 6;
		f = &lf;
	}
	std::set<int> items;
	wr->queryRect(x, y, w, h, f, items);
	lua_createtable(L,items.size(),0);
	int n = 0;
	for (std::set<int>::iterator it = items.begin(); it != items.end(); it++) {
		lua_rawgeti(L, -2, *it);
		lua_rawseti(L, -2, ++n);
	}
	lua_remove(L, -2);
	lua_pushinteger(L,n);
	return 2;
}

static int worldQueryCube(lua_State *L) {
	int nac= lua_gettop(L);
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	bool hasFilter=false;
	if ((8<=nac)&&!lua_isnoneornil(L, 8)) {
		luaL_checktype(L, 8, LUA_TFUNCTION);
		hasFilter=true;
	}
	assertIsCube(L, 2, 3, 4, 5, 6, 7);
	lua_getfield(L, 1, "__itemsr");

	double x = luaL_checknumber(L, 2);
	double y = luaL_checknumber(L, 3);
	double z = luaL_checknumber(L, 4);
	double w = luaL_checknumber(L, 5);
	double h = luaL_checknumber(L, 6);
	double d = luaL_checknumber(L, 7);
	ItemFilter *f = NULL;
	LuaItemFilter lf;
	lf.L = L;
	lf.itemsr = -1;
	if (hasFilter) {
		lf.func = 8;
		f = &lf;
	}
	std::set<int> items;
	wr->queryCube(x, y, z, w, h, d, f, items);
	lua_createtable(L,items.size(),0);
	int n = 0;
	for (std::set<int>::iterator it = items.begin(); it != items.end(); it++) {
		lua_rawgeti(L, -2, *it);
		lua_rawseti(L, -2, ++n);
	}
	lua_remove(L, -2);
	lua_pushinteger(L,n);
	return 2;
}

static int worldQueryPoint(lua_State *L) {
	int nac= lua_gettop(L);
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	bool hasFilter=false;
	int fctPos=wr->d3?5:4;
	if ((fctPos<=nac)&&!lua_isnoneornil(L, fctPos)) {
		luaL_checktype(L, fctPos, LUA_TFUNCTION);
		hasFilter=true;
	}
	lua_getfield(L, 1, "__itemsr");

	double x = luaL_checknumber(L, 2);
	double y = luaL_checknumber(L, 3);
	double z = (wr->d3)?luaL_checknumber(L, 4):0;
	ItemFilter *f = NULL;
	LuaItemFilter lf;
	lf.L = L;
	lf.itemsr = -1;
	if (hasFilter) {
		lf.func = fctPos;
		f = &lf;
	}
	std::set<int> items;
	if (wr->d3)
		wr->queryPoint3(x, y, z, f, items);
	else
		wr->queryPoint(x, y, f, items);
	lua_createtable(L,items.size(),0);
	int n = 0;
	for (std::set<int>::iterator it = items.begin(); it != items.end(); it++) {
		lua_rawgeti(L, -2, *it);
		lua_rawseti(L, -2, ++n);
	}
	lua_remove(L, -2);
	lua_pushinteger(L,n);
	return 2;
}

static int worldQuerySegment(lua_State *L) {
	int nac= lua_gettop(L);
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	bool hasFilter=false;
	int fctPos=wr->d3?8:6;
	if ((fctPos<=nac)&&!lua_isnoneornil(L, fctPos)) {
		luaL_checktype(L, fctPos, LUA_TFUNCTION);
		hasFilter=true;
	}
	lua_getfield(L, 1, "__itemsr");

	double x1 = luaL_checknumber(L, 2);
	double y1 = luaL_checknumber(L, 3);
	double z1,x2,y2,z2;
	if (wr->d3) {
		z1 = luaL_checknumber(L, 4);
		x2 = luaL_checknumber(L, 5);
		y2 = luaL_checknumber(L, 6);
		z2 = luaL_checknumber(L, 7);
	}
	else
	{
		x2 = luaL_checknumber(L, 4);
		y2 = luaL_checknumber(L, 5);
		z1=z2=0;
	}
	ItemFilter *f = NULL;
	LuaItemFilter lf;
	lf.L = L;
	lf.itemsr = -1;
	if (hasFilter) {
		lf.func = fctPos;
		f = &lf;
	}
	std::set<int> items;
	if (wr->d3)
		wr->querySegment3(x1, y1, z1, x2, y2, z2, f, items);
	else
		wr->querySegment(x1, y1, x2, y2, f, items);
	lua_createtable(L,items.size(),0);
	int n = 0;
	for (std::set<int>::iterator it = items.begin(); it != items.end(); it++) {
		lua_rawgeti(L, -2, *it);
		lua_rawseti(L, -2, ++n);
	}
	lua_remove(L, -2);
	lua_pushinteger(L,n);
	return 2;
}

static int worldQuerySegmentWithCoords(lua_State *L) {
	int nac= lua_gettop(L);
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	bool hasFilter=false;
	int fctPos=wr->d3?8:6;
	if ((fctPos<=nac)&&!lua_isnoneornil(L, fctPos)) {
		luaL_checktype(L, fctPos, LUA_TFUNCTION);
		hasFilter=true;
	}
	lua_getfield(L, 1, "__itemsr");

	double x1 = luaL_checknumber(L, 2);
	double y1 = luaL_checknumber(L, 3);
	double z1,x2,y2,z2;
	if (wr->d3) {
		z1 = luaL_checknumber(L, 4);
		x2 = luaL_checknumber(L, 5);
		y2 = luaL_checknumber(L, 6);
		z2 = luaL_checknumber(L, 7);
	}
	else
	{
		x2 = luaL_checknumber(L, 4);
		y2 = luaL_checknumber(L, 5);
		z1=z2=0;
	}
	ItemFilter *f = NULL;
	LuaItemFilter lf;
	lf.L = L;
	lf.itemsr = -1;
	if (hasFilter) {
		lf.func = fctPos;
		f = &lf;
	}
	std::vector<ItemInfo> items;
	if (wr->d3)
		wr->querySegmentWithCoords3(x1, y1, z1, x2, y2, z2, f, items);
	else
		wr->querySegmentWithCoords(x1, y1, x2, y2, f, items);
	lua_createtable(L,items.size(),0);
	int n = 0;
	for (std::vector<ItemInfo>::iterator it = items.begin(); it != items.end();
			it++) {
		lua_createtable(L,0,7);
		lua_rawgeti(L, -3, (*it).item);
		lua_setfield(L, -2, "item");
		lua_pushnumber(L, (*it).ti1);
		lua_setfield(L, -2, "ti1");
		lua_pushnumber(L, (*it).ti2);
		lua_setfield(L, -2, "ti2");
		lua_pushnumber(L, (*it).x1);
		lua_setfield(L, -2, "x1");
		lua_pushnumber(L, (*it).y1);
		lua_setfield(L, -2, "y1");
		lua_pushnumber(L, (*it).x2);
		lua_setfield(L, -2, "x2");
		lua_pushnumber(L, (*it).y2);
		lua_setfield(L, -2, "y2");
		if (wr->d3) {
			lua_pushnumber(L, (*it).z1);
			lua_setfield(L, -2, "z1");
			lua_pushnumber(L, (*it).z2);
			lua_setfield(L, -2, "z2");
		}
		lua_rawseti(L, -2, ++n);
	}
	lua_remove(L, -2);
	lua_pushinteger(L,n);
	return 2;
}

static int worldAdd(lua_State *L) {
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	if (wr->d3)
		assertIsCube(L, 3, 4, 5,6,7,8);
	else
		assertIsRect(L, 3, 4, 5,6);
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	if (!lua_isnil(L, -1)) {
		lua_pushfstring(L, "Item %s added to the world twice.",
				luaL_tostring(L, 2));
		lua_error(L);
	}
	lua_pop(L, 1);
	int item = wr->allocateId();
	double x = luaL_checknumber(L, 3);
	double y = luaL_checknumber(L, 4);
	double z,w,h,d;
	if (wr->d3)
	{
		z = luaL_checknumber(L, 5);
		w = luaL_checknumber(L, 6);
		h = luaL_checknumber(L, 7);
		d = luaL_checknumber(L, 8);
		wr->add3(item, x, y, z, w, h, d);
	}
	else {
		w = luaL_checknumber(L, 5);
		h = luaL_checknumber(L, 6);
		wr->add(item, x, y, w, h);
	}
	lua_pushvalue(L, 2);
	lua_pushinteger(L, item);
	lua_settable(L, -3);
	lua_getfield(L, 1, "__itemsr");
	lua_pushvalue(L, 2);
	lua_rawseti(L, -2, item);
	lua_pop(L, 2);
	lua_pushvalue(L, 2);
	return 1;
}

static int worldRemove(lua_State *L) {
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	if (lua_isnil(L, -1)) {
		lua_pushfstring(L,
				"Item %s must be added to the world before getting its rect. Use world:add(item, x,y,w,h) to add it first.",
				luaL_tostring(L, 2));
		lua_error(L);
	}
	int item = lua_tonumber(L, -1);
	lua_pop(L, 1);
	lua_pushvalue(L, 2);
	lua_pushnil(L);
	lua_settable(L, -3);
	lua_getfield(L, 1, "__itemsr");
	lua_pushnil(L);
	lua_rawseti(L, -2, item);
	lua_pop(L, 2);
	wr->remove(item);
	return 0;
}

static int worldUpdate(lua_State *L) {
	bool hasA5=!lua_isnoneornil(L,5);
	bool hasA6=!lua_isnoneornil(L,6);
	bool hasA7=!lua_isnoneornil(L,7);
	bool hasA8=!lua_isnoneornil(L,8);
	assertNumber(L, 3, "x");
	assertNumber(L, 4, "y");
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	double x = luaL_checknumber(L, 3);
	double y = luaL_checknumber(L, 4);
	double z,w,h,d;
	if (wr->d3)
	{
		assertNumber(L, 5, "z");
		z = luaL_checknumber(L, 5);
		if (hasA6)
			assertIsPositiveNumber(L, 6, "w");
		if (hasA7)
			assertIsPositiveNumber(L, 7, "h");
		if (hasA8)
			assertIsPositiveNumber(L, 8, "d");
		w = hasA6?luaL_checknumber(L, 6):-1;
		h = hasA7?luaL_checknumber(L, 7):-1;
		d = hasA8?luaL_checknumber(L, 8):-1;
	}
	else {
		if (hasA5)
			assertIsPositiveNumber(L, 5, "w");
		if (hasA6)
			assertIsPositiveNumber(L, 6, "h");
		w = hasA5?luaL_checknumber(L, 5):-1;
		h = hasA6?luaL_checknumber(L, 6):-1;
		z=d=0;
	}
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	if (lua_isnil(L, -1)) {
		lua_pushfstring(L,
				"Item %s must be added to the world before getting its rect. Use world:add(item, x,y,w,h) to add it first.",
				luaL_tostring(L, 2));
		lua_error(L);
	}
	int item = lua_tonumber(L, -1);
	lua_pop(L, 2);
	if (wr->d3)
		wr->update3(item, x, y, z, w, h, d);
	else
		wr->update(item, x, y, w, h);
	return 0;
}

static int worldMove(lua_State *L) {
	int nac= lua_gettop(L);
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	int fctPos=(wr->d3)?6:5;

	bool hasFilter=false;
	if ((fctPos<=nac)&&!lua_isnoneornil(L, fctPos)) {
		luaL_checktype(L, fctPos, LUA_TFUNCTION);
		hasFilter=true;
	}
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	if (lua_isnil(L, -1)) {
		lua_pushfstring(L,
				"Item %s must be added to the world before getting its rect. Use world:add(item, x,y,w,h) to add it first.",
				luaL_tostring(L, 2));
		lua_error(L);
	}
	int item = lua_tonumber(L, -1);
	lua_pop(L, 2);
	double x = luaL_checknumber(L, 3);
	double y = luaL_checknumber(L, 4);
	double z = (wr->d3)?luaL_checknumber(L, 5):0;

	ColFilter *f = NULL;
	LuaColFilter lf;
	lf.L = L;
	lf.itemsr = -1;
	if (hasFilter) {
		lf.func = fctPos;
		f = &lf;
	}
	double ax, ay, az;
	lua_getfield(L, 1, "__itemsr");
	std::vector<Collision> items;
	if (wr->d3)
		wr->move3(item, x, y, z, f, ax, ay, az, items);
    else {
		wr->move(item, x, y, f, ax, ay, items);
        az=0;
    }
	int n = 0;
	lua_createtable(L,items.size(),0);
	lua_insert(L,-2);
	for (std::vector<Collision>::iterator it = items.begin(); it != items.end();
			it++) {
		lua_createtable(L,0,10);
		lua_rawgeti(L, -2, (*it).item);
		lua_setfield(L, -2, "item");
		lua_rawgeti(L, -2, (*it).other);
		lua_setfield(L, -2, "other");
		lua_pushstring(L, (*it).type);
		lua_setfield(L, -2, "type");
		lua_pushboolean(L, (*it).overlaps);
		lua_setfield(L, -2, "overlaps");
		lua_pushnumber(L, (*it).ti);
		lua_setfield(L, -2, "ti");

		lua_createtable(L,0,2);
		lua_pushnumber(L, (*it).move.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).move.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).move.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "move");
		lua_createtable(L,0,2);
		lua_pushnumber(L, (*it).normal.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).normal.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).normal.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "normal");
		lua_createtable(L,0,2);
		lua_pushnumber(L, (*it).touch.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).touch.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).touch.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "touch");

		if ((!strcmp((*it).type, "bounce")) || (!strcmp((*it).type, "slide"))) {
			lua_createtable(L,0,2);
			lua_pushnumber(L, (*it).response.x);
			lua_setfield(L, -2, "x");
			lua_pushnumber(L, (*it).response.y);
			lua_setfield(L, -2, "y");
			if (wr->d3) {
				lua_pushnumber(L, (*it).response.z);
				lua_setfield(L, -2, "z");
			}
			lua_setfield(L, -2, (*it).type);
		}

		lua_createtable(L,0,4);
		lua_pushnumber(L, (*it).itemRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).itemRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, (*it).itemRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, (*it).itemRect.h);
		lua_setfield(L, -2, "h");
		if (wr->d3) {
			lua_pushnumber(L, (*it).itemRect.z);
			lua_setfield(L, -2, "z");
			lua_pushnumber(L, (*it).itemRect.d);
			lua_setfield(L, -2, "d");
		}
		lua_setfield(L, -2, "itemRect");
		lua_createtable(L,0,4);
		lua_pushnumber(L, (*it).otherRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).otherRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, (*it).otherRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, (*it).otherRect.h);
		lua_setfield(L, -2, "h");
		if (wr->d3) {
			lua_pushnumber(L, (*it).otherRect.z);
			lua_setfield(L, -2, "z");
			lua_pushnumber(L, (*it).otherRect.d);
			lua_setfield(L, -2, "d");
		}
		lua_setfield(L, -2, "otherRect");

		lua_rawseti(L, -3, ++n);
	}
	lua_pop(L, 1);
	lua_pushnumber(L, ax);
	lua_pushnumber(L, ay);
	if (wr->d3) {
		lua_pushnumber(L, az);
		lua_pushvalue(L, -4);
		lua_remove(L, -5);
		lua_pushinteger(L, n);

		return 5;
	}
	else {
		lua_pushvalue(L, -3);
		lua_remove(L, -4);
		lua_pushinteger(L, n);

		return 4;
	}
}

static int worldCheck(lua_State *L) {
	int nac= lua_gettop(L);
	World *wr = (World *) g_getInstance(L, "BumpWorld", 1);
	int fctPos=(wr->d3)?6:5;

	bool hasFilter=false;
	if ((fctPos<=nac)&&!lua_isnoneornil(L, fctPos)) {
		luaL_checktype(L, fctPos, LUA_TFUNCTION);
		hasFilter=true;
	}
	lua_getfield(L, 1, "__items");
	lua_pushvalue(L, 2);
	lua_gettable(L, -2);
	if (lua_isnil(L, -1)) {
		lua_pushfstring(L,
				"Item %s must be added to the world before getting its rect. Use world:add(item, x,y,w,h) to add it first.",
				luaL_tostring(L, 2));
		lua_error(L);
	}
	int item = lua_tonumber(L, -1);
	lua_pop(L, 2);
	double x = luaL_checknumber(L, 3);
	double y = luaL_checknumber(L, 4);
	double z = (wr->d3)?luaL_checknumber(L, 5):0;

	ColFilter *f = NULL;
	LuaColFilter lf;
	lf.L = L;
	lf.itemsr = -1;
	if (hasFilter) {
		lf.func = fctPos;
		f = &lf;
	}
	double ax, ay, az;
	lua_getfield(L, 1, "__itemsr");
	std::vector<Collision> items;
	if (wr->d3)
		wr->check3(item, x, y, z, f, ax, ay, az, items);
	else
		wr->check(item, x, y, f, ax, ay, items);
	int n = 0;
	lua_createtable(L,items.size(),0);
	lua_insert(L,-2);
	for (std::vector<Collision>::iterator it = items.begin(); it != items.end();
			it++) {
		lua_createtable(L,0,10);
		lua_rawgeti(L, -2, (*it).item);
		lua_setfield(L, -2, "item");
		lua_rawgeti(L, -2, (*it).other);
		lua_setfield(L, -2, "other");
		lua_pushstring(L, (*it).type);
		lua_setfield(L, -2, "type");
		lua_pushboolean(L, (*it).overlaps);
		lua_setfield(L, -2, "overlaps");
		lua_pushnumber(L, (*it).ti);
		lua_setfield(L, -2, "ti");

		lua_createtable(L,0,2);
		lua_pushnumber(L, (*it).move.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).move.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).move.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "move");
		lua_createtable(L,0,2);
		lua_pushnumber(L, (*it).normal.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).normal.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).normal.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "normal");
		lua_createtable(L,0,2);
		lua_pushnumber(L, (*it).touch.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).touch.y);
		lua_setfield(L, -2, "y");
		if (wr->d3) {
			lua_pushnumber(L, (*it).touch.z);
			lua_setfield(L, -2, "z");
		}
		lua_setfield(L, -2, "touch");

		if ((!strcmp((*it).type, "bounce")) || (!strcmp((*it).type, "slide"))) {
			lua_createtable(L,0,2);
			lua_pushnumber(L, (*it).response.x);
			lua_setfield(L, -2, "x");
			lua_pushnumber(L, (*it).response.y);
			lua_setfield(L, -2, "y");
			if (wr->d3) {
				lua_pushnumber(L, (*it).response.z);
				lua_setfield(L, -2, "z");
			}
			lua_setfield(L, -2, (*it).type);
		}

		lua_createtable(L,0,4);
		lua_pushnumber(L, (*it).itemRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).itemRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, (*it).itemRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, (*it).itemRect.h);
		lua_setfield(L, -2, "h");
		if (wr->d3) {
			lua_pushnumber(L, (*it).itemRect.z);
			lua_setfield(L, -2, "z");
			lua_pushnumber(L, (*it).itemRect.d);
			lua_setfield(L, -2, "d");
		}
		lua_setfield(L, -2, "itemRect");
		lua_createtable(L,0,4);
		lua_pushnumber(L, (*it).otherRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, (*it).otherRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, (*it).otherRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, (*it).otherRect.h);
		lua_setfield(L, -2, "h");
		if (wr->d3) {
			lua_pushnumber(L, (*it).otherRect.z);
			lua_setfield(L, -2, "z");
			lua_pushnumber(L, (*it).otherRect.d);
			lua_setfield(L, -2, "d");
		}
		lua_setfield(L, -2, "otherRect");

		lua_rawseti(L, -3, ++n);
	}
	lua_pop(L, 1);
	lua_pushnumber(L, ax);
	lua_pushnumber(L, ay);
	if (wr->d3) {
		lua_pushnumber(L, az);
		lua_pushvalue(L, -4);
		lua_remove(L, -5);
		lua_pushinteger(L, n);

		return 5;
	}
	else {
		lua_pushvalue(L, -3);
		lua_remove(L, -4);
		lua_pushinteger(L, n);

		return 4;
	}
}

static int rectGetNearestCorner(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double w1 = luaL_checknumber(L, 3);
	double h1 = luaL_checknumber(L, 4);
	double px = luaL_checknumber(L, 5);
	double py = luaL_checknumber(L, 6);
	double nx, ny;
	rect_getNearestCorner(x1, y1, w1, h1, px, py, nx, ny);
	lua_pushnumber(L, nx);
	lua_pushnumber(L, ny);
	return 2;
}

static int rectGetSegmentIntersectionIndices(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double w1 = luaL_checknumber(L, 3);
	double h1 = luaL_checknumber(L, 4);
	double x2 = luaL_checknumber(L, 5);
	double y2 = luaL_checknumber(L, 6);
	double w2 = luaL_checknumber(L, 7);
	double h2 = luaL_checknumber(L, 8);
	double ti1=0, ti2=1, nx1, ny1, nx2, ny2;
	rect_getSegmentIntersectionIndices(x1, y1, w1, h1, x2, y2, w2, h2, ti1, ti2,
			nx1, ny1, nx2, ny2);
	lua_pushnumber(L, ti1);
	lua_pushnumber(L, ti2);
	lua_pushnumber(L, nx1);
	lua_pushnumber(L, ny1);
	lua_pushnumber(L, nx2);
	lua_pushnumber(L, ny2);
	return 6;
}

static int rectGetDiff(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double w1 = luaL_checknumber(L, 3);
	double h1 = luaL_checknumber(L, 4);
	double x2 = luaL_checknumber(L, 5);
	double y2 = luaL_checknumber(L, 6);
	double w2 = luaL_checknumber(L, 7);
	double h2 = luaL_checknumber(L, 8);

	double x, y, w, h;

	rect_getDiff(x1, y1, w1, h1, x2, y2, w2, h2, x, y, w, h);

	lua_pushnumber(L, x);
	lua_pushnumber(L, y);
	lua_pushnumber(L, w);
	lua_pushnumber(L, h);
	return 4;
}

static int rectContainsPoint(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double w1 = luaL_checknumber(L, 3);
	double h1 = luaL_checknumber(L, 4);
	double x2 = luaL_checknumber(L, 5);
	double y2 = luaL_checknumber(L, 6);
	lua_pushboolean(L, rect_containsPoint(x1, y1, w1, h1, x2, y2));
	return 1;
}

static int rectIsIntersecting(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double w1 = luaL_checknumber(L, 3);
	double h1 = luaL_checknumber(L, 4);
	double x2 = luaL_checknumber(L, 5);
	double y2 = luaL_checknumber(L, 6);
	double w2 = luaL_checknumber(L, 7);
	double h2 = luaL_checknumber(L, 8);
	lua_pushboolean(L, rect_isIntersecting(x1, y1, w1, h1, x2, y2, w2, h2));
	return 1;
}

static int rectGetSquareDistance(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double w1 = luaL_checknumber(L, 3);
	double h1 = luaL_checknumber(L, 4);
	double x2 = luaL_checknumber(L, 5);
	double y2 = luaL_checknumber(L, 6);
	double w2 = luaL_checknumber(L, 7);
	double h2 = luaL_checknumber(L, 8);
	lua_pushnumber(L, rect_getSquareDistance(x1, y1, w1, h1, x2, y2, w2, h2));
	return 1;
}

static int rectDetectCollision(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double w1 = luaL_checknumber(L, 3);
	double h1 = luaL_checknumber(L, 4);
	double x2 = luaL_checknumber(L, 5);
	double y2 = luaL_checknumber(L, 6);
	double w2 = luaL_checknumber(L, 7);
	double h2 = luaL_checknumber(L, 8);
	double gx = luaL_checknumber(L, 9);
	double gy = luaL_checknumber(L, 10);
	Collision col;
	if (rect_detectCollision(x1, y1, w1, h1, x2, y2, w2, h2, gx, gy, col)) {
		lua_newtable(L);
		lua_pushboolean(L, col.overlaps);
		lua_setfield(L, -2, "overlaps");
		lua_pushnumber(L, col.ti);
		lua_setfield(L, -2, "ti");

		lua_newtable(L);
		lua_pushnumber(L, col.move.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.move.y);
		lua_setfield(L, -2, "y");
		lua_setfield(L, -2, "move");
		lua_newtable(L);
		lua_pushnumber(L, col.normal.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.normal.y);
		lua_setfield(L, -2, "y");
		lua_setfield(L, -2, "normal");
		lua_newtable(L);
		lua_pushnumber(L, col.touch.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.touch.y);
		lua_setfield(L, -2, "y");
		lua_setfield(L, -2, "touch");

		lua_newtable(L);
		lua_pushnumber(L, col.itemRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.itemRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, col.itemRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, col.itemRect.h);
		lua_setfield(L, -2, "h");
		lua_setfield(L, -2, "itemRect");
		lua_newtable(L);
		lua_pushnumber(L, col.otherRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.otherRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, col.otherRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, col.otherRect.h);
		lua_setfield(L, -2, "h");
		lua_setfield(L, -2, "otherRect");
		return 1;
	}
	return 0;
}

static int cubeGetNearestCorner(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double z1 = luaL_checknumber(L, 3);
	double w1 = luaL_checknumber(L, 4);
	double h1 = luaL_checknumber(L, 5);
	double d1 = luaL_checknumber(L, 6);
	double px = luaL_checknumber(L, 7);
	double py = luaL_checknumber(L, 8);
	double pz = luaL_checknumber(L, 9);
	double nx, ny, nz;
	cube_getNearestCorner(x1, y1, z1, w1, h1, d1, px, py, pz, nx, ny, nz);
	lua_pushnumber(L, nx);
	lua_pushnumber(L, ny);
	lua_pushnumber(L, nz);
	return 3;
}

static int cubeGetSegmentIntersectionIndices(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double z1 = luaL_checknumber(L, 3);
	double w1 = luaL_checknumber(L, 4);
	double h1 = luaL_checknumber(L, 5);
	double d1 = luaL_checknumber(L, 6);
	double x2 = luaL_checknumber(L, 7);
	double y2 = luaL_checknumber(L, 8);
	double z2 = luaL_checknumber(L, 9);
	double w2 = luaL_checknumber(L, 10);
	double h2 = luaL_checknumber(L, 11);
	double d2 = luaL_checknumber(L, 12);
	double ti1=0, ti2=1, nx1, ny1, nz1, nx2, ny2, nz2;
	cube_getSegmentIntersectionIndices(x1, y1, z1, w1, h1, d1, x2, y2, z2, w2, h2, d2, ti1, ti2,
			nx1, ny1, nz1, nx2, ny2, nz2);
	lua_pushnumber(L, ti1);
	lua_pushnumber(L, ti2);
	lua_pushnumber(L, nx1);
	lua_pushnumber(L, ny1);
	lua_pushnumber(L, nz1);
	lua_pushnumber(L, nx2);
	lua_pushnumber(L, ny2);
	lua_pushnumber(L, nz2);
	return 8;
}

static int cubeGetDiff(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double z1 = luaL_checknumber(L, 3);
	double w1 = luaL_checknumber(L, 4);
	double h1 = luaL_checknumber(L, 5);
	double d1 = luaL_checknumber(L, 6);
	double x2 = luaL_checknumber(L, 7);
	double y2 = luaL_checknumber(L, 8);
	double z2 = luaL_checknumber(L, 9);
	double w2 = luaL_checknumber(L, 10);
	double h2 = luaL_checknumber(L, 11);
	double d2 = luaL_checknumber(L, 12);

	double x, y, z, w, h, d;

	cube_getDiff(x1, y1, z1, w1, h1, d1, x2, y2, z2, w2, h2, d2, x, y, z, w, h, d);

	lua_pushnumber(L, x);
	lua_pushnumber(L, y);
	lua_pushnumber(L, z);
	lua_pushnumber(L, w);
	lua_pushnumber(L, h);
	lua_pushnumber(L, d);
	return 6;
}

static int cubeContainsPoint(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double z1 = luaL_checknumber(L, 3);
	double w1 = luaL_checknumber(L, 4);
	double h1 = luaL_checknumber(L, 5);
	double d1 = luaL_checknumber(L, 6);
	double x2 = luaL_checknumber(L, 7);
	double y2 = luaL_checknumber(L, 8);
	double z2 = luaL_checknumber(L, 9);
	lua_pushboolean(L, cube_containsPoint(x1, y1, z1, w1, h1, d1, x2, y2, z2));
	return 1;
}

static int cubeIsIntersecting(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double z1 = luaL_checknumber(L, 3);
	double w1 = luaL_checknumber(L, 4);
	double h1 = luaL_checknumber(L, 5);
	double d1 = luaL_checknumber(L, 6);
	double x2 = luaL_checknumber(L, 7);
	double y2 = luaL_checknumber(L, 8);
	double z2 = luaL_checknumber(L, 9);
	double w2 = luaL_checknumber(L, 10);
	double h2 = luaL_checknumber(L, 11);
	double d2 = luaL_checknumber(L, 12);
	lua_pushboolean(L, cube_isIntersecting(x1, y1, z1, w1, h1, d1, x2, y2, z2, w2, h2, d2));
	return 1;
}

static int cubeGetSquareDistance(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double z1 = luaL_checknumber(L, 3);
	double w1 = luaL_checknumber(L, 4);
	double h1 = luaL_checknumber(L, 5);
	double d1 = luaL_checknumber(L, 6);
	double x2 = luaL_checknumber(L, 7);
	double y2 = luaL_checknumber(L, 8);
	double z2 = luaL_checknumber(L, 9);
	double w2 = luaL_checknumber(L, 10);
	double h2 = luaL_checknumber(L, 11);
	double d2 = luaL_checknumber(L, 12);
	lua_pushnumber(L, cube_getCubeDistance(x1, y1, z1, w1, h1, d1, x2, y2, z2, w2, h2, d2));
	return 1;
}

static int cubeDetectCollision(lua_State *L) {
	double x1 = luaL_checknumber(L, 1);
	double y1 = luaL_checknumber(L, 2);
	double z1 = luaL_checknumber(L, 3);
	double w1 = luaL_checknumber(L, 4);
	double h1 = luaL_checknumber(L, 5);
	double d1 = luaL_checknumber(L, 6);
	double x2 = luaL_checknumber(L, 7);
	double y2 = luaL_checknumber(L, 8);
	double z2 = luaL_checknumber(L, 9);
	double w2 = luaL_checknumber(L, 10);
	double h2 = luaL_checknumber(L, 11);
	double d2 = luaL_checknumber(L, 12);
	double gx = luaL_checknumber(L, 13);
	double gy = luaL_checknumber(L, 14);
	double gz = luaL_checknumber(L, 15);
	Collision col;
	if (cube_detectCollision(x1, y1, z1, w1, h1, d1, x2, y2, z2, w2, h2, d2, gx, gy, gz, col)) {
		lua_newtable(L);
		lua_pushboolean(L, col.overlaps);
		lua_setfield(L, -2, "overlaps");
		lua_pushnumber(L, col.ti);
		lua_setfield(L, -2, "ti");

		lua_newtable(L);
		lua_pushnumber(L, col.move.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.move.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, col.move.z);
		lua_setfield(L, -2, "z");
		lua_setfield(L, -2, "move");
		lua_newtable(L);
		lua_pushnumber(L, col.normal.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.normal.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, col.normal.z);
		lua_setfield(L, -2, "z");
		lua_setfield(L, -2, "normal");
		lua_newtable(L);
		lua_pushnumber(L, col.touch.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.touch.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, col.touch.z);
		lua_setfield(L, -2, "z");
		lua_setfield(L, -2, "touch");

		lua_newtable(L);
		lua_pushnumber(L, col.itemRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.itemRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, col.itemRect.z);
		lua_setfield(L, -2, "z");
		lua_pushnumber(L, col.itemRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, col.itemRect.h);
		lua_setfield(L, -2, "h");
		lua_pushnumber(L, col.itemRect.d);
		lua_setfield(L, -2, "d");
		lua_setfield(L, -2, "itemRect");
		lua_newtable(L);
		lua_pushnumber(L, col.otherRect.x);
		lua_setfield(L, -2, "x");
		lua_pushnumber(L, col.otherRect.y);
		lua_setfield(L, -2, "y");
		lua_pushnumber(L, col.otherRect.z);
		lua_setfield(L, -2, "z");
		lua_pushnumber(L, col.otherRect.w);
		lua_setfield(L, -2, "w");
		lua_pushnumber(L, col.otherRect.h);
		lua_setfield(L, -2, "h");
		lua_pushnumber(L, col.otherRect.d);
		lua_setfield(L, -2, "d");
		lua_setfield(L, -2, "otherRect");
		return 1;
	}
	return 0;
}

static int bumpNewWorld(lua_State *L) {
    if (!lua_isnoneornil(L,1))
        assertIsPositiveNumber(L, 1, "cellSize");
    if (!lua_isnoneornil(L,2))
        assertIsPositiveNumber(L, 2, "precision");
    bool d3=lua_toboolean(L,3);
    int cs = luaL_optinteger(L, 1, 64);
    double precision = luaL_optnumber(L, 2, 0);
    lua_getglobal(L, "BumpWorld");
	lua_getfield(L, -1, "new");
	lua_call(L, 0, 1);
	World *w = (World *) g_getInstance(L, "BumpWorld", -1);
	w->cellSize = cs;
    w->precision = precision;
	w->d3=d3;
	return 1;
}

static int loader(lua_State *L) {
	const luaL_Reg worldFuncs[] =
			{
					//    {"addResponse", worldAddResponse}, Don't implement
					{ "project", worldProject },
					{ "countCells", worldCountCells },
					{ "hasItem", worldHasItem },
					{ "getItems", worldGetItems },
					{ "countItems", worldCountItems },
					{ "getRect", worldGetRect },
					{ "getCube", worldGetCube },
					{ "toWorld", worldToWorld },
					{ "toCell", worldToCell },
					{ "queryRect", worldQueryRect },
					{ "queryCube", worldQueryCube },
					{ "queryPoint", worldQueryPoint },
					{ "querySegment", worldQuerySegment },
					{ "querySegmentWithCoords",	worldQuerySegmentWithCoords },
					{ "add", worldAdd },
					{ "remove", worldRemove },
					{ "update", worldUpdate },
					{ "move", worldMove },
					{ "check", worldCheck },
					{ NULL, NULL }, };

	g_createClass(L, "BumpWorld", NULL, worldCreate, worldDestruct, worldFuncs);

	const luaL_Reg bumpFuncs[] =
			{ { "newWorld", bumpNewWorld }, { NULL, NULL }, };

	lua_newtable(L);
	luaL_register(L, NULL, bumpFuncs);

	const luaL_Reg rectFuncs[] =
			{ { "getNearestCorner", rectGetNearestCorner }, {
					"getSegmentIntersectionIndices",
					rectGetSegmentIntersectionIndices }, { "getDiff",
					rectGetDiff }, { "containsPoint", rectContainsPoint }, {
					"isIntersecting", rectIsIntersecting }, {
					"getSquareDistance", rectGetSquareDistance }, {
					"detectCollision", rectDetectCollision }, { NULL, NULL }, };

	lua_newtable(L);
	luaL_register(L, NULL, rectFuncs);
	lua_setfield(L, -2, "rect");

	const luaL_Reg cubeFuncs[] =
			{ { "getNearestCorner", cubeGetNearestCorner }, {
					"getSegmentIntersectionIndices",
					cubeGetSegmentIntersectionIndices }, { "getDiff",
					cubeGetDiff }, { "containsPoint", cubeContainsPoint }, {
					"isIntersecting", cubeIsIntersecting }, {
					"getSquareDistance", cubeGetSquareDistance }, {
					"detectCollision", cubeDetectCollision }, { NULL, NULL }, };

	lua_newtable(L);
	luaL_register(L, NULL, cubeFuncs);
	lua_setfield(L, -2, "cube");

	return 1;
}

static void g_initializePlugin(lua_State *L) {
	lua_getglobal(L, "package");
	lua_getfield(L, -1, "preload");

	lua_pushcnfunction(L, loader,"plugin_init_cbump");
	lua_setfield(L, -2, "cbump");

	lua_pop(L, 2);
}

static void g_deinitializePlugin(lua_State *L) {
	UNUSED(L);
}
REGISTER_PLUGIN_NAMED("Bump", "3.1.7", bump)
