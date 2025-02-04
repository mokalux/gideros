/*
 * OggDec.h
 *
 *  Created on: 20 sept. 2019
 *      Author: Nico
 */

#ifndef PLUGINS_OGG_SOURCE_COMMON_OGGENC_H_
#define PLUGINS_OGG_SOURCE_COMMON_OGGENC_H_
#include <ogg/ogg.h>
#include <stdlib.h>
#include "gplugin.h"

class OggEnc {
public:
    int Format;
    struct VideoBuffer {
    	int width;
        int height;
        int stride;
        void *data;
    };
    struct VideoFrame {
        VideoBuffer y;
        VideoBuffer u;
        VideoBuffer v;
    };
    virtual ~OggEnc() {};
    virtual bool PacketOut(ogg_packet *op)=0;
    virtual bool InitAudio(unsigned int channels, unsigned int rate, float quality)
	{
		G_UNUSED(channels);
		G_UNUSED(rate);
		G_UNUSED(quality);
		return false;
	};
    virtual bool GenHeaderPage(ogg_stream_state *os) {
        G_UNUSED(os);
        return false;
    };
	virtual void WriteAudio(void *buffer,size_t size)
	{
		G_UNUSED(buffer);
		G_UNUSED(size);
	};
    virtual bool InitVideo(float rate,unsigned int width, unsigned int height, int format, float quality)
    {
        G_UNUSED(rate);
        G_UNUSED(width);
        G_UNUSED(height);
        G_UNUSED(format);
        G_UNUSED(quality);
        return false;
    };
    virtual void EncodeVideoFrame(ogg_int64_t gpos,VideoFrame *frame,bool last)
    {
        G_UNUSED(gpos);
        G_UNUSED(frame);
        G_UNUSED(last);
    }
};

struct OggEncType {
    int type; //1=Audio, 2=Video
    OggEnc *(*build)();
};


extern "C" {
G_DLLEXPORT void register_oggenc(const char *name,OggEncType codec);
G_DLLEXPORT void unregister_oggenc(const char *name);
OggEnc *build_oggenc(const char *name);
}
#endif /* PLUGINS_OGG_SOURCE_COMMON_OGGDEC_H_ */
