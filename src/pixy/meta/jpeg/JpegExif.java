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
 * JpegExif.java
 *
 * Who   Date       Description
 * ====  =======    =================================================
 * WY    03Feb2015  Initial creation
 */

package pixy.meta.jpeg;

import java.io.IOException;
import java.io.OutputStream;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;

import pixy.image.jpeg.Marker;
import pixy.image.tiff.ASCIIField;
import pixy.image.tiff.IFD;
import pixy.image.tiff.LongField;
import pixy.image.tiff.TiffField;
import pixy.image.tiff.TiffTag;
import pixy.io.IOUtils;
import pixy.io.MemoryCacheRandomAccessOutputStream;
import pixy.io.RandomAccessOutputStream;
import pixy.io.WriteStrategyMM;
import pixy.io.WriteStrategyII;
import pixy.meta.exif.Exif;
import pixy.meta.exif.ExifTag;

public class JpegExif extends Exif {

	public JpegExif() {
		;
	}
	
	public JpegExif(byte[] data) {
		super(data);
	}
	
	private void createImageIFD() {
		// Create Image IFD (IFD0)
		imageIFD = new IFD();
		TiffField<?> tiffField = new ASCIIField(TiffTag.IMAGE_DESCRIPTION.getValue(), "Exif created by JPEGTweaker");
		imageIFD.addField(tiffField);
		String softWare = "JPEGTweaker 1.0";
		tiffField = new ASCIIField(TiffTag.SOFTWARE.getValue(), softWare);
		imageIFD.addField(tiffField);
		DateFormat formatter = new SimpleDateFormat("yyyy:MM:dd HH:mm:ss");
		tiffField = new ASCIIField(TiffTag.DATETIME.getValue(), formatter.format(new Date()));
		imageIFD.addField(tiffField);		
	}
	
	/** 
	 * Write the EXIF data to the OutputStream
	 * 
	 * @param os OutputStream
	 * @throws Exception 
	 */
	@Override
	public void write(OutputStream os) throws IOException {
		ensureDataRead();
		// Wraps output stream with a RandomAccessOutputStream
		RandomAccessOutputStream randOS = new MemoryCacheRandomAccessOutputStream(os);
		// Write JPEG the EXIF data
		// Writes APP1 marker
		IOUtils.writeShortMM(os, Marker.APP1.getValue());		
		// TIFF structure starts here
		short tiffID = 0x2a; //'*'
		randOS.setWriteStrategy((preferredEndian == IOUtils.BIG_ENDIAN)? WriteStrategyMM.getInstance():WriteStrategyII.getInstance());
		randOS.writeShort(preferredEndian);
		randOS.writeShort(tiffID);
		// First IFD offset relative to TIFF structure
		randOS.seek(0x04);
		randOS.writeInt(FIRST_IFD_OFFSET);
		// Writes IFDs
		randOS.seek(FIRST_IFD_OFFSET);
		if(imageIFD == null) createImageIFD();
		// Attach EXIIF and/or GPS SubIFD to main image IFD
		if(exifSubIFD != null) {
			imageIFD.addField(new LongField(TiffTag.EXIF_SUB_IFD.getValue(), new int[]{0})); // Place holder
			imageIFD.addChild(TiffTag.EXIF_SUB_IFD, exifSubIFD);
			if(interopSubIFD != null) {
				exifSubIFD.addField(new LongField(ExifTag.EXIF_INTEROPERABILITY_OFFSET.getValue(), new int[]{0})); // Place holder
				exifSubIFD.addChild(ExifTag.EXIF_INTEROPERABILITY_OFFSET, interopSubIFD);			
			}
		}
		if(gpsSubIFD != null) {
			imageIFD.addField(new LongField(TiffTag.GPS_SUB_IFD.getValue(), new int[]{0})); // Place holder
			imageIFD.addChild(TiffTag.GPS_SUB_IFD, gpsSubIFD);
		}
		int offset = imageIFD.write(randOS, FIRST_IFD_OFFSET);
		if(thumbnail != null && thumbnail.containsImage()) {
			imageIFD.setNextIFDOffset(randOS, offset);
			randOS.seek(offset); // Set the stream pointer to the correct position
			thumbnail.write(randOS);
		}
		// Now it's time to update the segment length
		int length = (int)randOS.getLength();
		// Update segment length
		IOUtils.writeShortMM(os, length + 8);
		// Add EXIF identifier with trailing bytes [0x00,0x00].
		byte[] exif = {0x45, 0x78, 0x69, 0x66, 0x00, 0x00};
		IOUtils.write(os, exif);
		// Dump randOS to normal output stream and we are done!
		randOS.seek(0);
		randOS.writeToStream(length);
		randOS.shallowClose();
	}
}
