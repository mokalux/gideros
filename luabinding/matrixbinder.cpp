#include <string.h>
#include "matrixbinder.h"
#include "stackchecker.h"
#include <transform.h>
#include "Shaders.h"
#include <math.h>

#ifndef M_PI
#define M_PI       3.14159265358979323846
#endif

MatrixBinder::MatrixBinder(lua_State* L)
{
	Binder binder(L);
	
	static const luaL_Reg functionList[] = {
        {"getM11", getM11},
        {"getM12", getM12},
        {"getM21", getM21},
        {"getM22", getM22},
		{"getTx", getTx},
		{"getTy", getTy},
		{"getTz", getTz},

        {"setM11", setM11},
        {"setM12", setM12},
        {"setM21", setM21},
        {"setM22", setM22},
		{"setTx", setTx},
		{"setTy", setTy},
		{"setTz", setTz},

		{"setElements", setElements},
		{"getElements", getElements},
		{"setMatrix", setMatrix},
		{"getMatrix", getMatrix},
		{"orthographicProjection", orthographicProjection},
		{"perspectiveProjection", perspectiveProjection},
		{"scale",scale},
		{"rotate",rotate},
		{"translate",translate},
		{"multiply",multiply},
		{"invert",invert},
		{"transformPoint",transformPoint},
		{"transformVector",transformVector},
		{"duplicate",duplicate},
		{"fromSRT",fromSRT},
        {"lookAt",lookAt},
        {"toQuaternion",toQuaternion},

		{"getX", getX},
		{"getY", getY},
		{"getZ", getZ},
		{"getRotationZ", getRotationZ},
		{"getRotationX", getRotationX},
		{"getRotationY", getRotationY},
		{"getScaleX", getScaleX},
		{"getScaleY", getScaleY},
		{"getScaleZ", getScaleZ},
		{"setX", setX},
		{"setY", setY},
		{"setZ", setZ},
		{"setRotationZ", setRotationZ},
		{"setRotationX", setRotationX},
		{"setRotationY", setRotationY},
		{"setScaleX", setScaleX},
		{"setScaleY", setScaleY},
		{"setScaleZ", setScaleZ},
		{"setPosition", setPosition},
		{"getPosition", getPosition},
		{"setRotation", setRotation},
		{"getRotation", getRotation},
        {"setAnchorPosition", setAnchorPosition},
        {"getAnchorPosition", getAnchorPosition},
        {"setScale", setScale},
        {"getScale", getScale},

		{NULL, NULL},
	};

	binder.createClass("Matrix", NULL, create, destruct, functionList);
}

struct TVector {
	Vector4 v;
	enum { VT_VEC, VT_ARG } type;
	bool vec4;
	int get(lua_State *L,int idx,bool opt=false,bool v4=false);
	int ret(lua_State *L);
};

int TVector::get(lua_State *L,int idx,bool opt,bool v4)
{
	v.w=1;
	vec4=v4;
	int bidx=idx;
	if (opt&&lua_isnoneornil(L,idx)) return 0;
	const float *vf=lua_tovector(L,idx);
	if (vf) {
		v.x=vf[0];
		v.y=vf[1];
		v.z=vf[2];
#if LUA_VECTOR_SIZE == 4
		if (vec4&&(!isnan(vf[3])))
			v.w=vf[3];
#endif
		type=VT_VEC;
		return 1;
	}
	v.x=luaL_checknumber(L,idx++);
	v.y=luaL_checknumber(L,idx++);
	v.z=luaL_optnumber(L,idx++,0.0);
	if (vec4)
		v.w=luaL_optnumber(L,idx++,1.0);
	type=VT_ARG;
	return idx-bidx;
}

int TVector::ret(lua_State *L)
{
	if (type==VT_VEC) {
#if LUA_VECTOR_SIZE == 4
		lua_pushvector(L,v.x,v.y,v.z,vec4?v.w:0);
#else
		lua_pushvector(L,v.x,v.y,v.z);
#endif
		return 1;
	}
	lua_pushnumber(L,v.x);
	lua_pushnumber(L,v.y);
	lua_pushnumber(L,v.z);
	if (vec4)
		lua_pushnumber(L,v.w);
	return vec4?4:3;
}

int MatrixBinder::create(lua_State* L)
{
	StackChecker checker(L, "MatrixBinder::create", 1);

	Binder binder(L);

	lua_Number m11 = luaL_optnumber(L, 1, 1);
	lua_Number m12 = luaL_optnumber(L, 2, 0);
	lua_Number m21 = luaL_optnumber(L, 3, 0);
	lua_Number m22 = luaL_optnumber(L, 4, 1);
	lua_Number tx = luaL_optnumber(L, 5, 0);
	lua_Number ty = luaL_optnumber(L, 6, 0);

	Transform *t=new Transform();
	t->setMatrix(m11, m12, m21, m22, tx, ty);

    binder.pushInstance("Matrix", t);

	return 1;
}

int MatrixBinder::destruct(void *p)
{
	void *ptr = GIDEROS_DTOR_UDATA(p);
	Transform* matrix = static_cast<Transform*>(ptr);
	delete matrix;

	return 0;
}


int MatrixBinder::getM11(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

    lua_pushnumber(L, matrix->matrix()[0]);

	return 1;
}
int MatrixBinder::getM12(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

    lua_pushnumber(L, matrix->matrix()[4]);

	return 1;
}
int MatrixBinder::getM21(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

    lua_pushnumber(L, matrix->matrix()[1]);

	return 1;
}
int MatrixBinder::getM22(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

    lua_pushnumber(L, matrix->matrix()[5]);

	return 1;
}
int MatrixBinder::getTx(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_pushnumber(L, matrix->matrix()[12]);

	return 1;
}

int MatrixBinder::getTy(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_pushnumber(L, matrix->matrix()[13]);

	return 1;
}

int MatrixBinder::getTz(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_pushnumber(L, matrix->matrix()[14]);

	return 1;
}


int MatrixBinder::setM11(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	float m[16];
	memcpy(&m,matrix->matrix().data(),sizeof(float)*16);
	m[0]=luaL_checknumber(L, 2);
	matrix->setMatrix(m);

	return 0;
}
int MatrixBinder::setM12(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	float m[16];
	memcpy(&m,matrix->matrix().data(),sizeof(float)*16);
	m[4]=luaL_checknumber(L, 2);
	matrix->setMatrix(m);

	return 0;
}
int MatrixBinder::setM21(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	float m[16];
	memcpy(&m,matrix->matrix().data(),sizeof(float)*16);
	m[1]=luaL_checknumber(L, 2);
	matrix->setMatrix(m);

	return 0;
}
int MatrixBinder::setM22(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	float m[16];
	memcpy(&m,matrix->matrix().data(),sizeof(float)*16);
	m[5]=luaL_checknumber(L, 2);
	matrix->setMatrix(m);

	return 0;
}
int MatrixBinder::setTx(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	float m[16];
	memcpy(&m,matrix->matrix().data(),sizeof(float)*16);
	m[12]=luaL_checknumber(L, 2);
	matrix->setMatrix(m);

	return 0;
}
int MatrixBinder::setTy(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	float m[16];
	memcpy(&m,matrix->matrix().data(),sizeof(float)*16);
	m[13]=luaL_checknumber(L, 2);
	matrix->setMatrix(m);

	return 0;
}

int MatrixBinder::setTz(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	float m[16];
	memcpy(&m,matrix->matrix().data(),sizeof(float)*16);
	m[14]=luaL_checknumber(L, 2);
	matrix->setMatrix(m);

	return 0;
}

int MatrixBinder::getElements(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	const float *m=matrix->matrix().data();

    lua_pushnumber(L, m[0]);
    lua_pushnumber(L, m[4]);
    lua_pushnumber(L, m[1]);
    lua_pushnumber(L, m[5]);
	lua_pushnumber(L, m[12]);
	lua_pushnumber(L, m[13]);

	return 6;
}

int MatrixBinder::setElements(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_Number m11 = luaL_optnumber(L, 2, 1);
	lua_Number m12 = luaL_optnumber(L, 3, 0);
	lua_Number m21 = luaL_optnumber(L, 4, 0);
	lua_Number m22 = luaL_optnumber(L, 5, 1);
	lua_Number tx = luaL_optnumber(L, 6, 0);
	lua_Number ty = luaL_optnumber(L, 7, 0);

    matrix->setMatrix(m11, m12, m21, m22, tx, ty);

	return 0;
}

int MatrixBinder::getMatrix(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	const float *m=matrix->matrix().data();

	for (int k=0;k<16;k++)
		lua_pushnumber(L, m[k]);

	return 16;
}

int MatrixBinder::setMatrix(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	float m[16];
	for (int k=0;k<16;k++)
		m[k] = luaL_optnumber(L, 2+k, ((k%5)==0)?1:0);

    matrix->setMatrix(m);

	return 0;
}

int MatrixBinder::orthographicProjection(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_Number l=luaL_checknumber(L,2);
	lua_Number r=luaL_checknumber(L,3);
	lua_Number b=luaL_checknumber(L,4);
	lua_Number t=luaL_checknumber(L,5);
	lua_Number n=luaL_checknumber(L,6);
	lua_Number f=luaL_checknumber(L,7);
	matrix->setMatrix(ShaderEngine::Engine->setOrthoFrustum(l,r,b,t,n,f,false).data());

	return 0;
}

int MatrixBinder::perspectiveProjection(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	if (lua_gettop(L)==7) //Full version (left/right,bottom/top,near/far)
	{
		lua_Number l=luaL_checknumber(L,2);
		lua_Number r=luaL_checknumber(L,3);
		lua_Number b=luaL_checknumber(L,4);
		lua_Number t=luaL_checknumber(L,5);
		lua_Number n=luaL_checknumber(L,6);
		lua_Number f=luaL_checknumber(L,7);
		matrix->setMatrix(ShaderEngine::Engine->setFrustum(l,r,b,t,n,f).data());
	}
	else //Simplified version (fov,aspect ratio,near/far)
	{
		lua_Number fov=luaL_checknumber(L,2);
		lua_Number ar=luaL_checknumber(L,3);
		lua_Number n=luaL_checknumber(L,4);
		lua_Number f=luaL_checknumber(L,5);
		float hw=tan(fov * M_PI / 360.0)*n;
		float hh=hw/ar;
		matrix->setMatrix(ShaderEngine::Engine->setFrustum(-hw,hw,-hh,hh,n,f).data());
	}
	return 0;
}

int MatrixBinder::scale(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	TVector in;
	in.get(L,2);
	Matrix4 m=matrix->matrix();
	m.scale(in.v.x,in.v.y,in.v.z);
	matrix->setMatrix(m.data());
	return 0;
}

int MatrixBinder::translate(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	TVector in;
	in.get(L,2);

	Matrix4 m=matrix->matrix();
	m.translate(in.v.x,in.v.y,in.v.z);
	matrix->setMatrix(m.data());
	return 0;
}

int MatrixBinder::rotate(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_Number a=luaL_checknumber(L,2);
	TVector in;
	in.get(L,3);
	Matrix4 m=matrix->matrix();
	m.rotate(a,in.v.x,in.v.y,in.v.z);
	matrix->setMatrix(m.data());
	return 0;
}

int MatrixBinder::multiply(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));
	Transform* matrix2 = static_cast<Transform*>(binder.getInstance("Matrix", 2));

	Matrix4 m=matrix->matrix();
	m=m*matrix2->matrix();
	matrix->setMatrix(m.data());
	return 0;
}

int MatrixBinder::invert(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));
	Matrix4 m=matrix->matrix();
	m=m.inverse();
	matrix->setMatrix(m.data());
	return 0;
}

int MatrixBinder::transformPoint(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));
	Matrix4 m=matrix->matrix();
	TVector in;

	in.get(L,2,false,true);
	in.v=m*in.v;
	return in.ret(L);
}

int MatrixBinder::transformVector(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));
	Matrix4 m=matrix->matrix();
	TVector in;

	in.get(L,2);
	in.v.z=1;
	Vector4 z(0,0,0,1);
	Vector4 res=m*in.v;
	Vector4 rz=m*z;
	in.v=res-rz;
	return in.ret(L);
}

int MatrixBinder::getX(lua_State* L)
{
	StackChecker checker(L, "getX", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->x());

	return 1;
}

int MatrixBinder::getY(lua_State* L)
{
	StackChecker checker(L, "getY", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->y());

	return 1;
}

int MatrixBinder::getZ(lua_State* L)
{
	StackChecker checker(L, "getZ", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->z());

	return 1;
}

int MatrixBinder::getRotationZ(lua_State* L)
{
	StackChecker checker(L, "getRotation", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->rotationZ());

	return 1;
}

int MatrixBinder::getRotationX(lua_State* L)
{
	StackChecker checker(L, "getRotationX", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->rotationX());

	return 1;
}

int MatrixBinder::getRotationY(lua_State* L)
{
	StackChecker checker(L, "getRotationY", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->rotationY());

	return 1;
}

int MatrixBinder::getScaleX(lua_State* L)
{
	StackChecker checker(L, "getScaleX", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->scaleX());

	return 1;
}

int MatrixBinder::getScaleY(lua_State* L)
{
	StackChecker checker(L, "getScaleY", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->scaleY());

	return 1;
}

int MatrixBinder::getScaleZ(lua_State* L)
{
	StackChecker checker(L, "getScaleZ", 1);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	lua_pushnumber(L, sprite->scaleZ());

	return 1;
}

int MatrixBinder::setX(lua_State* L)
{
	StackChecker checker(L, "setX");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double x = luaL_checknumber(L, 2);
	sprite->setX(x);

	return 0;
}

int MatrixBinder::setY(lua_State* L)
{
	StackChecker checker(L, "setY");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double y = luaL_checknumber(L, 2);
	sprite->setY(y);

	return 0;
}

int MatrixBinder::setZ(lua_State* L)
{
	StackChecker checker(L, "setZ");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double z = luaL_checknumber(L, 2);
	sprite->setZ(z);

	return 0;
}

int MatrixBinder::setRotationZ(lua_State* L)
{
	StackChecker checker(L, "setRotationZ");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double rotation = luaL_checknumber(L, 2);
	sprite->setRotationZ(rotation);

	return 0;
}

int MatrixBinder::setRotationX(lua_State* L)
{
	StackChecker checker(L, "setRotationX");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double rotation = luaL_checknumber(L, 2);
	sprite->setRotationX(rotation);

	return 0;
}

int MatrixBinder::setRotationY(lua_State* L)
{
	StackChecker checker(L, "setRotationY");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double rotation = luaL_checknumber(L, 2);
	sprite->setRotationY(rotation);

	return 0;
}

int MatrixBinder::setScaleX(lua_State* L)
{
	StackChecker checker(L, "setScaleX");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double scaleX = luaL_checknumber(L, 2);
	sprite->setScaleX(scaleX);

	return 0;
}

int MatrixBinder::setScaleY(lua_State* L)
{
	StackChecker checker(L, "setScaleY");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double scaleY = luaL_checknumber(L, 2);
	sprite->setScaleY(scaleY);

	return 0;
}

int MatrixBinder::setScaleZ(lua_State* L)
{
	StackChecker checker(L, "setScaleZ");

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix"));

	double scaleZ = luaL_checknumber(L, 2);
	sprite->setScaleZ(scaleZ);

	return 0;
}

int MatrixBinder::setPosition(lua_State* L)
{
	StackChecker checker(L, "MatrixBinder::setPosition", 0);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	const float *v=lua_tovector(L,2);
	if (v)
		sprite->setXYZ(v[0], v[1], v[2]);
	else {
		lua_Number x = luaL_checknumber(L, 2);
		lua_Number y = luaL_checknumber(L, 3);
		if (lua_isnoneornil(L, 4))
			sprite->setXY(x, y);
		else
		{
			lua_Number z = luaL_checknumber(L, 4);
			sprite->setXYZ(x, y, z);
		}
	}

	return 0;
}

int MatrixBinder::getPosition(lua_State* L)
{
	StackChecker checker(L, "MatrixBinder::getPosition", 3);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_pushnumber(L, sprite->x());
	lua_pushnumber(L, sprite->y());
	lua_pushnumber(L, sprite->z());

	return 3;
}

int MatrixBinder::setRotation(lua_State* L)
{
	StackChecker checker(L, "MatrixBinder::setRotation", 0);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));
	const float *v=lua_tovector(L,2);
	if (v)
		sprite->setRotation(v[0], v[1], v[2]);
	else {
		lua_Number x = luaL_optnumber(L, 2,sprite->rotationX());
		lua_Number y = luaL_optnumber(L, 3,sprite->rotationY());
		lua_Number z = luaL_optnumber(L, 4,sprite->rotationZ());
		sprite->setRotation(x, y, z);
	}

	return 0;
}

int MatrixBinder::getRotation(lua_State* L)
{
	StackChecker checker(L, "MatrixBinder::getRotation", 3);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_pushnumber(L, sprite->rotationX());
	lua_pushnumber(L, sprite->rotationY());
	lua_pushnumber(L, sprite->rotationZ());

	return 3;
}

int MatrixBinder::setAnchorPosition(lua_State* L)
{
    StackChecker checker(L, "MatrixBinder::setAnchorPosition", 0);

    Binder binder(L);
    Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	const float *v=lua_tovector(L,2);
	if (v)
		sprite->setRefXYZ(v[0], v[1], v[2]);
	else {
		lua_Number x = luaL_checknumber(L, 2);
		lua_Number y = luaL_checknumber(L, 3);
		if (lua_isnoneornil(L, 4))
			sprite->setRefXY(x, y);
		else
		{
			lua_Number z = luaL_checknumber(L, 4);
			sprite->setRefXYZ(x, y, z);
		}
	}
    return 0;
}

int MatrixBinder::getAnchorPosition(lua_State* L)
{
    StackChecker checker(L, "MatrixBinder::getAnchorPosition", 3);

    Binder binder(L);
    Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));

    lua_pushnumber(L, sprite->refX());
    lua_pushnumber(L, sprite->refY());
    lua_pushnumber(L, sprite->refZ());

    return 3;
}



int MatrixBinder::setScale(lua_State* L)
{
	StackChecker checker(L, "MatrixBinder::setScale", 0);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	const float *v=lua_tovector(L,2);
	if (v)
		sprite->setScaleXYZ(v[0], v[1], v[2]);
	else {
		lua_Number x = luaL_checknumber(L, 2);
		lua_Number y = lua_isnoneornil(L, 3) ? x : luaL_checknumber(L, 3);
		if (lua_isnoneornil(L, 4)) //No Z
			sprite->setScaleXY(x, y); // Only scale X and Y
		else
		{
			lua_Number z = luaL_checknumber(L, 4);
			sprite->setScaleXYZ(x, y, z);
		}
	}
	return 0;
}

int MatrixBinder::getScale(lua_State* L)
{
	StackChecker checker(L, "MatrixBinder::getScale", 3);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	lua_pushnumber(L, sprite->scaleX());
	lua_pushnumber(L, sprite->scaleY());
	lua_pushnumber(L, sprite->scaleZ());

	return 3;
}

int MatrixBinder::toQuaternion(lua_State* L)
{
	StackChecker checker(L, "MatrixBinder::toQuaternion", 4);

	Binder binder(L);
	Transform* sprite = static_cast<Transform*>(binder.getInstance("Matrix", 1));
	float w,x,y,z;
	sprite->toQuaternion(w, x, y, z);

	lua_pushnumber(L, w);
	lua_pushnumber(L, x);
	lua_pushnumber(L, y);
	lua_pushnumber(L, z);

	return 4;
}

int MatrixBinder::duplicate(lua_State* L)
{
	Binder binder(L);
	Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

	Transform *t=new Transform();
	t->setMatrix(matrix->matrix().data());
    binder.pushInstance("Matrix", t);

	return 1;
}

int MatrixBinder::fromSRT(lua_State* L)
{
	Binder binder(L);
	bool rev=lua_toboolean(L,2);
	luaL_checktype(L,1,LUA_TTABLE);
	//Fields
	lua_getfield(L,1,"t");
	if (lua_isnoneornil(L,-1)) {
		lua_pop(L,1);
		lua_getfield(L,1,"translate");
		if (lua_isnoneornil(L,-1)) {
			lua_pop(L,1);
			lua_getfield(L,1,"position");
		}
	}
	lua_getfield(L,1,"r");
	if (lua_isnoneornil(L,-1)) {
		lua_pop(L,1);
		lua_getfield(L,1,"rotation");
	}
	lua_getfield(L,1,"s");
	if (lua_isnoneornil(L,-1)) {
		lua_pop(L,1);
		lua_getfield(L,1,"scale");
	}

	Transform *t=new Transform();
	Matrix4 mt;
	if (rev&&(!lua_isnoneornil(L,-3))) {
		lua_rawgeti(L,-3,1);
		lua_rawgeti(L,-4,2);
		lua_rawgeti(L,-5,3);
		mt.translate(luaL_optnumber(L,-3,0), luaL_optnumber(L,-2,0), luaL_optnumber(L,-1,0));
		lua_pop(L,3);
	} else {
		if (!lua_isnoneornil(L,-1)) {
			lua_rawgeti(L,-1,1);
			lua_rawgeti(L,-2,2);
			lua_rawgeti(L,-3,3);
			mt.scale(luaL_optnumber(L,-3,0), luaL_optnumber(L,-2,0), luaL_optnumber(L,-1,0));
			lua_pop(L,3);
		}
	}
	if (!lua_isnoneornil(L,-2)) {
		lua_rawgeti(L,-2,1);
		lua_rawgeti(L,-3,2);
		lua_rawgeti(L,-4,3);
		lua_rawgeti(L,-5,4);
		float X=luaL_optnumber(L,-4,0);
		float Y=luaL_optnumber(L,-3,0);
		float Z=luaL_optnumber(L,-2,0);
		float W=luaL_optnumber(L,-1,0);
		lua_pop(L,4);

		float L=sqrt(X*X+Y*Y+Z*Z+W*W);
		X/=L; Y/=L; Z/=L; W/=L;
		float xx,xy,xz,xw,yy,yz,yw,zz,zw;
		float m00,m01,m02,m10,m11,m12,m20,m21,m22;
		xx      = X * X;
		xy      = X * Y;
		xz      = X * Z;
		xw      = X * W;

		yy      = Y * Y;
		yz      = Y * Z;
		yw      = Y * W;

		zz      = Z * Z;
		zw      = Z * W;

		m00  = 1 - 2 * ( yy + zz );
		m01  =     2 * ( xy - zw );
		m02 =     2 * ( xz + yw );
		m10  =     2 * ( xy + zw );
		m11  = 1 - 2 * ( xx + zz );
		m12  =     2 * ( yz - xw );
		m20  =     2 * ( xz - yw );
		m21  =     2 * ( yz + xw );
		m22 = 1 - 2 * ( xx + yy );

		Matrix4 rm(m00,m10,m20,0,m01,m11,m21,0,m02,m12,m22,0,0,0,0,1);
		mt=rm*mt;
	}

	if (rev&&(!lua_isnoneornil(L,-1))) {
		lua_rawgeti(L,-1,1);
		lua_rawgeti(L,-2,2);
		lua_rawgeti(L,-3,3);
		mt.scale(luaL_optnumber(L,-3,0), luaL_optnumber(L,-2,0), luaL_optnumber(L,-1,0));
		lua_pop(L,3);
	} else {
		if (!lua_isnoneornil(L,-3)) {
			lua_rawgeti(L,-3,1);
			lua_rawgeti(L,-4,2);
			lua_rawgeti(L,-5,3);
			mt.translate(luaL_optnumber(L,-3,0), luaL_optnumber(L,-2,0), luaL_optnumber(L,-1,0));
			lua_pop(L,3);
		}
	}

	t->setMatrix(mt.data());
    binder.pushInstance("Matrix", t);

	return 1;
}

int MatrixBinder::lookAt(lua_State* L)
{
    StackChecker checker(L, "MatrixBinder::lookAt", 0);

    Binder binder(L);
    Transform* matrix = static_cast<Transform*>(binder.getInstance("Matrix", 1));

    TVector e,t,s;
    int idx=2;
    idx+=e.get(L,idx);
    idx+=t.get(L,idx);
    idx+=s.get(L,idx);

    matrix->lookAt(e.v.x,e.v.y,e.v.z,t.v.x,t.v.y,t.v.z,s.v.x,s.v.y,s.v.z);

    return 0;
}
