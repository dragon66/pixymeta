/**
 * Copyright (c) 2015 by Wen Yu.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Any modifications to this file must keep this entire header intact.
 *
 * Change History - most recent changes go on top of previous changes
 *
 * MetadataUtils.java
 *
 * Who   Date       Description
 * ====  =========  ==============================================================
 * WY    13Mar2015  Initial creation
 */

package pixy.util;

import java.awt.image.BufferedImage;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

import pixy.meta.adobe.ImageResourceID;
import pixy.meta.adobe._8BIM;
import cafe.image.writer.ImageWriter;
import cafe.image.writer.JPEGWriter;
import cafe.io.IOUtils;

/** 
 * This utility class contains static methods 
 * to help with image manipulation and IO. 
 * <p>
 * 
 * @author Wen Yu, yuwen_66@yahoo.com
 * @version 1.1.2 04/02/2012
 */
public class MetadataUtils {
	
	/**
	 * Wraps a BufferedImage inside a Photoshop _8BIM
	 * @param thumbnail input thumbnail image
	 * @return a Photoshop _8BMI
	 * @throws IOException
	 */
	public static _8BIM createThumbnail8BIM(BufferedImage thumbnail) throws IOException {
		// Create memory buffer to write data
		ByteArrayOutputStream bout = new ByteArrayOutputStream();
		// Compress the thumbnail
		ImageWriter writer = new JPEGWriter();
		try {
			writer.write(thumbnail, bout);
		} catch (Exception e) {
			e.printStackTrace();
		}
		byte[] data = bout.toByteArray();
		bout.reset();
		// Write thumbnail format
		IOUtils.writeIntMM(bout, 1); // 1 = kJpegRGB. We are going to write JPEG format thumbnail
		// Write thumbnail dimension
		int width = thumbnail.getWidth();
		int height = thumbnail.getHeight();
		IOUtils.writeIntMM(bout, width);
		IOUtils.writeIntMM(bout, height);
		// Padded row bytes = (width * bits per pixel + 31) / 32 * 4.
		int bitsPerPixel = 24;
		int planes = 1;
		int widthBytes = (width*bitsPerPixel + 31)/32*4;
		IOUtils.writeIntMM(bout, widthBytes);
		// Total size = widthbytes * height * planes
		IOUtils.writeIntMM(bout, widthBytes*height*planes);
		// Size after compression. Used for consistency check.
		IOUtils.writeIntMM(bout, data.length);
		IOUtils.writeShortMM(bout, bitsPerPixel);
		IOUtils.writeShortMM(bout, planes);
		bout.write(data);
		// Create 8BIM
		_8BIM bim = new _8BIM(ImageResourceID.THUMBNAIL_RESOURCE_PS5, "thumbnail", bout.toByteArray());
	
		return bim;
	}
	
	// Prevent from instantiation
	private MetadataUtils(){}
}