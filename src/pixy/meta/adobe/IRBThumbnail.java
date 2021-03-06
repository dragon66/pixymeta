/**
 * Copyright (C) 2014-2019 by Wen Yu.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Any modifications to this file must keep this entire header intact.
 * 
 * Change History - most recent changes go on top of previous changes
 *
 * IRBThumbnail.java
 *
 * Who   Date       Description
 * ====  =========  ===========================================================
 * WY    27Apr2015  Added copy constructor
 * WY    13Apr2015  Moved related code to ThumbnailResource
 * WY    10Apr2015  Implemented base class Thumbnail abstract method write()
 * WY    13Mar2015  Initial creation for IRBReader to encapsulate IRB thumbnail
 */

package pixy.meta.adobe;

import java.awt.image.BufferedImage;
import java.io.IOException;
import java.io.OutputStream;

import pixy.meta.Thumbnail;
import pixy.util.MetadataUtils;

/** 
 * Photoshop Image Resource Block thumbnail wrapper.
 *
 * @author Wen Yu, yuwen_66@yahoo.com 
 * @version 1.0 01/10/2015   
 */
public class IRBThumbnail extends Thumbnail {
	
	public IRBThumbnail() { ; }
	
	public IRBThumbnail(BufferedImage thumbnail) {
		super(thumbnail);
	}
	
	public IRBThumbnail(int width, int height, int dataType, byte[] compressedThumbnail) {
		super(width, height, dataType, compressedThumbnail);
	}
	
	public IRBThumbnail(IRBThumbnail other) { // Copy constructor
		this.dataType = other.dataType;
		this.height = other.height;
		this.width = other.width;
		this.thumbnail = other.thumbnail;
		this.compressedThumbnail = other.compressedThumbnail;
	}

	@Override
	public void write(OutputStream os) throws IOException {
		if(getDataType() == Thumbnail.DATA_TYPE_KJpegRGB) { // Compressed old-style JPEG format
			os.write(getCompressedImage());
		} else if(getDataType() == Thumbnail.DATA_TYPE_KRawRGB) {
			BufferedImage thumbnail = getRawImage();
			if(thumbnail == null) throw new IllegalArgumentException("Expected raw data thumbnail does not exist!");
			MetadataUtils.saveAsJPEG(thumbnail, os, writeQuality);
		}
	}
 }
