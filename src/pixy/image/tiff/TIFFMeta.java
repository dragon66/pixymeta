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
 * TIFFMeta.java
 *
 * Who   Date       Description
 * ====  =========  =================================================
 * WY    13Mar2015  Initial creation
 */

package pixy.image.tiff;

import java.awt.color.ICC_Profile;
import java.awt.image.BufferedImage;
import java.io.ByteArrayOutputStream;
import java.io.EOFException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.w3c.dom.Document;

import pixy.meta.Metadata;
import pixy.meta.MetadataType;
import pixy.meta.adobe.IRB;
import pixy.meta.adobe.IRBReader;
import pixy.meta.adobe.IRBThumbnail;
import pixy.meta.adobe.ImageResourceID;
import pixy.meta.adobe.XMP;
import pixy.meta.adobe._8BIM;
import pixy.meta.exif.Exif;
import pixy.meta.exif.ExifTag;
import pixy.meta.exif.GPSTag;
import pixy.meta.exif.InteropTag;
import pixy.meta.exif.TiffExif;
import pixy.meta.icc.ICCProfile;
import pixy.meta.iptc.IPTC;
import pixy.meta.iptc.IPTCDataSet;
import pixy.meta.iptc.IPTCReader;
import pixy.util.MetadataUtils;
import cafe.image.ImageIO;
import cafe.image.ImageType;
import cafe.image.jpeg.Marker;
import cafe.image.tiff.ASCIIField;
import cafe.image.tiff.ByteField;
import cafe.image.tiff.DoubleField;
import cafe.image.tiff.FieldType;
import cafe.image.tiff.FloatField;
import cafe.image.tiff.IFD;
import cafe.image.tiff.IFDField;
import cafe.image.tiff.LongField;
import cafe.image.tiff.RationalField;
import cafe.image.tiff.SRationalField;
import cafe.image.tiff.ShortField;
import cafe.image.tiff.Tag;
import cafe.image.tiff.TiffField;
import cafe.image.tiff.TiffFieldEnum;
import cafe.image.tiff.TiffTag;
import cafe.image.tiff.UndefinedField;
import cafe.image.writer.ImageWriter;
import cafe.io.IOUtils;
import cafe.io.RandomAccessInputStream;
import cafe.io.RandomAccessOutputStream;
import cafe.io.ReadStrategyII;
import cafe.io.ReadStrategyMM;
import cafe.io.WriteStrategyII;
import cafe.io.WriteStrategyMM;
import cafe.string.StringUtils;
import cafe.string.XMLUtils;
import cafe.util.ArrayUtils;
import static cafe.image.writer.TIFFWriter.*;

public class TIFFMeta {
	private static int copyHeader(RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {		
		rin.seek(STREAM_HEAD);
		// First 2 bytes determine the byte order of the file, "MM" or "II"
	    short endian = rin.readShort();
	
		if (endian == IOUtils.BIG_ENDIAN) {
		    System.out.println("Byte order: Motorola BIG_ENDIAN");
		    rin.setReadStrategy(ReadStrategyMM.getInstance());
		    rout.setWriteStrategy(WriteStrategyMM.getInstance());
		} else if(endian == IOUtils.LITTLE_ENDIAN) {
		    System.out.println("Byte order: Intel LITTLE_ENDIAN");
		    rin.setReadStrategy(ReadStrategyII.getInstance());
		    rout.setWriteStrategy(WriteStrategyII.getInstance());
		} else {
			rin.close();
			rout.close();
			throw new RuntimeException("Invalid TIFF byte order");
	    } 
		
		rout.writeShort(endian);
		// Read TIFF identifier
		rin.seek(0x02);
		short tiff_id = rin.readShort();
		
		if(tiff_id!=0x2a)//"*" 42 decimal
		{
		   rin.close();
		   rout.close();
		   throw new RuntimeException("Invalid TIFF identifier");
		}
		
		rout.writeShort(tiff_id);
		rin.seek(OFFSET_TO_WRITE_FIRST_IFD_OFFSET);
		
		return rin.readInt();
	}
	
	private static List<IPTCDataSet> copyIPTCDataSet(List<IPTCDataSet> iptcs, byte[] data) throws IOException {
		IPTC iptc = new IPTC(data);
		// Shallow copy the map
		Map<String, List<IPTCDataSet>> dataSetMap = new HashMap<String, List<IPTCDataSet>>(iptc.getDataSet());
		for(IPTCDataSet set : iptcs)
			if(!set.allowMultiple())
				dataSetMap.remove(set.getName());
		for(List<IPTCDataSet> iptcList : dataSetMap.values())
			iptcs.addAll(iptcList);
		
		return iptcs;
	}
	
	private static TiffField<?> copyJPEGHufTable(RandomAccessInputStream rin, RandomAccessOutputStream rout, TiffField<?> field, int curPos) throws IOException
	{
		int[] data = field.getDataAsLong();
		int[] tmp = new int[data.length];
	
		for(int i = 0; i < data.length; i++) {
			rin.seek(data[i]);
			tmp[i] = curPos;
			byte[] htable = new byte[16];
			IOUtils.readFully(rin, htable);
			IOUtils.write(rout, htable);			
			curPos += 16;
			
			int numCodes = 0;
			
            for(int j = 0; j < 16; j++) {
                numCodes += htable[j]&0xff;
            }
            
            curPos += numCodes;
            
            htable = new byte[numCodes];
            IOUtils.readFully(rin, htable);
			IOUtils.write(rout, htable);
		}
		
		if(TiffTag.fromShort(field.getTag()) == TiffTag.JPEG_AC_TABLES)
			return new LongField(TiffTag.JPEG_AC_TABLES.getValue(), tmp);
	
		return new LongField(TiffTag.JPEG_DC_TABLES.getValue(), tmp);
	}
	
	private static void copyJPEGIFByteCount(RandomAccessInputStream rin, RandomAccessOutputStream rout, int offset, int outOffset) throws IOException 
	{		
		boolean finished = false;
		int length = 0;	
		short marker;
		Marker emarker;
		
		rin.seek(offset);
		rout.seek(outOffset);
		// The very first marker should be the start_of_image marker!	
		if(Marker.fromShort(IOUtils.readShortMM(rin)) != Marker.SOI)
		{
			System.out.println("Invalid JPEG image, expected SOI marker not found!");
			return;
		}
		
		System.out.println(Marker.SOI);
		IOUtils.writeShortMM(rout, Marker.SOI.getValue());
		
		marker = IOUtils.readShortMM(rin);
			
		while (!finished)
	    {	        
			if (Marker.fromShort(marker) == Marker.EOI)
			{
				System.out.println(Marker.EOI);
				IOUtils.writeShortMM(rout, marker);
				finished = true;
			}
		   	else // Read markers
			{
		   		emarker = Marker.fromShort(marker);
				System.out.println(emarker); 
				
				switch (emarker) {
					case JPG: // JPG and JPGn shouldn't appear in the image.
					case JPG0:
					case JPG13:
				    case TEM: // The only stand alone mark besides SOI, EOI, and RSTn. 
				    	marker = IOUtils.readShortMM(rin);
				    	break;
				    case SOS:						
						marker = copyJPEGSOS(rin, rout);
						break;
				    case PADDING:	
				    	int nextByte = 0;
				    	while((nextByte = rin.read()) == 0xff) {;}
				    	marker = (short)((0xff<<8)|nextByte);
				    	break;
				    default:
					    length = IOUtils.readUnsignedShortMM(rin);
					    byte[] buf = new byte[length - 2];
					    rin.read(buf);
					    IOUtils.writeShortMM(rout, marker);
					    IOUtils.writeShortMM(rout, length);
					    rout.write(buf);
					    marker = IOUtils.readShortMM(rin);					 
				}
			}
	    }
	}
	
	private static TiffField<?> copyJPEGQTable(RandomAccessInputStream rin, RandomAccessOutputStream rout, TiffField<?> field, int curPos) throws IOException
	{
		byte[] qtable = new byte[64];
		int[] data = field.getDataAsLong();
		int[] tmp = new int[data.length];
		
		for(int i = 0; i < data.length; i++) {
			rin.seek(data[i]);
			tmp[i] = curPos;
			IOUtils.readFully(rin, qtable);
			IOUtils.write(rout, qtable);
			curPos += 64;
		}
		
		return new LongField(TiffTag.JPEG_Q_TABLES.getValue(), tmp);
	}
	
	private static short copyJPEGSOS(RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException 
	{
		int len = IOUtils.readUnsignedShortMM(rin);
		byte buf[] = new byte[len - 2];
		IOUtils.readFully(rin, buf);
		IOUtils.writeShortMM(rout, Marker.SOS.getValue());
		IOUtils.writeShortMM(rout, len);
		rout.write(buf);		
		// Actual image data follow.
		int nextByte = 0;
		short marker = 0;	
		
		while((nextByte = IOUtils.read(rin)) != -1)
		{
			rout.write(nextByte);
			
			if(nextByte == 0xff)
			{
				nextByte = IOUtils.read(rin);
			    rout.write(nextByte);
			    
				if (nextByte == -1) {
					throw new IOException("Premature end of SOS segment!");					
				}								
				
				if (nextByte != 0x00)
				{
					marker = (short)((0xff<<8)|nextByte);
					
					switch (Marker.fromShort(marker)) {										
						case RST0:  
						case RST1:
						case RST2:
						case RST3:
						case RST4:
						case RST5:
						case RST6:
						case RST7:
							System.out.println(Marker.fromShort(marker));
							continue;
						default:
					}
					break;
				}
			}
		}
		
		if (nextByte == -1) {
			throw new IOException("Premature end of SOS segment!");
		}

		return marker;
	}
	
	/**
	 * @param offset offset to write page image data
	 * 
	 * @return the position where to write the IFD for the current image page
	 */
	private static int copyPageData(IFD ifd, int offset, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		// Move stream pointer to the right place
		rout.seek(offset);

		// Original image data start from these offsets.
		TiffField<?> stripOffSets = ifd.removeField(TiffTag.STRIP_OFFSETS);
		
		if(stripOffSets == null)
			stripOffSets = ifd.removeField(TiffTag.TILE_OFFSETS);
				
		TiffField<?> stripByteCounts = ifd.getField(TiffTag.STRIP_BYTE_COUNTS);
		
		if(stripByteCounts == null)
			stripByteCounts = ifd.getField(TiffTag.TILE_BYTE_COUNTS);	
		/* 
		 * Make sure this will work in the case when neither STRIP_OFFSETS nor TILE_OFFSETS presents.
		 * Not sure if this will ever happen for TIFF. JPEG EXIF data do not contain these fields. 
		 */
		if(stripOffSets != null) { 
			int[] counts = stripByteCounts.getDataAsLong();		
			int[] off = stripOffSets.getDataAsLong();
			int[] temp = new int[off.length];
			
			TiffField<?> tiffField = ifd.getField(TiffTag.COMPRESSION);
			
			// Uncompressed image with one strip or tile (may contain wrong StripByteCounts value)
			// Bug fix for uncompressed image with one strip and wrong StripByteCounts value
			if((tiffField == null ) || (tiffField != null && tiffField.getDataAsLong()[0] == 1)) { // Uncompressed data
				int planaryConfiguration = 1;
				
				tiffField = ifd.getField(TiffTag.PLANAR_CONFIGURATTION);		
				if(tiffField != null) planaryConfiguration = tiffField.getDataAsLong()[0];
				
				tiffField = ifd.getField(TiffTag.SAMPLES_PER_PIXEL);
				
				int samplesPerPixel = 1;
				if(tiffField != null) samplesPerPixel = tiffField.getDataAsLong()[0];
				
				// If there is only one strip/samplesPerPixel strips for PlanaryConfiguration = 2
				if((planaryConfiguration == 1 && off.length == 1) || (planaryConfiguration == 2 && off.length == samplesPerPixel))
				{
					int[] totalBytes2Read = getBytes2Read(ifd);
				
					for(int i = 0; i < off.length; i++)
						counts[i] = totalBytes2Read[i];					
				}				
			} // End of bug fix
			
			// We are going to write the image data first
			rout.seek(offset);
		
			// Copy image data from offset
			for(int i = 0; i < off.length; i++) {
				rin.seek(off[i]);
				byte[] buf = new byte[counts[i]];
				rin.readFully(buf);
				rout.write(buf);
				temp[i] = offset;
				offset += buf.length;
			}
						
			if(ifd.getField(TiffTag.STRIP_BYTE_COUNTS) != null)
				stripOffSets = new LongField(TiffTag.STRIP_OFFSETS.getValue(), temp);
			else
				stripOffSets = new LongField(TiffTag.TILE_OFFSETS.getValue(), temp);		
			ifd.addField(stripOffSets);		
		}
		
		// add copyright and software fields.
		String copyRight = "Copyright (c) Wen Yu, 2014 (yuwen_66@yahoo.com)\0";
		ifd.addField(new ASCIIField(TiffTag.COPYRIGHT.getValue(), copyRight));
		
		String softWare = "TIFFMeta 1.0\0";
		ifd.addField(new ASCIIField(TiffTag.SOFTWARE.getValue(), softWare));
		// End of copyright and software field.
	
		/* The following are added to work with old-style JPEG compression (type 6) */		
		/* One of the flavors (found in JPEG EXIF thumbnail IFD - IFD1) of the old JPEG compression contains this field */
		TiffField<?> jpegIFOffset = ifd.removeField(TiffTag.JPEG_INTERCHANGE_FORMAT);
		if(jpegIFOffset != null) {
			TiffField<?> jpegIFByteCount = ifd.removeField(TiffTag.JPEG_INTERCHANGE_FORMAT_LENGTH);			
			try {
				if(jpegIFByteCount != null) {
					rin.seek(jpegIFOffset.getDataAsLong()[0]);
					byte[] bytes2Read = new byte[jpegIFByteCount.getDataAsLong()[0]];
					rin.readFully(bytes2Read);
					rout.seek(offset);
					rout.write(bytes2Read);
					ifd.addField(jpegIFByteCount);
				} else {
					long startOffset = rout.getStreamPointer();
					copyJPEGIFByteCount(rin, rout, jpegIFOffset.getDataAsLong()[0], offset);
					long endOffset = rout.getStreamPointer();
					ifd.addField(new LongField(TiffTag.JPEG_INTERCHANGE_FORMAT_LENGTH.getValue(), new int[]{(int)(endOffset - startOffset)}));
				}
				jpegIFOffset = new LongField(TiffTag.JPEG_INTERCHANGE_FORMAT.getValue(), new int[]{offset});
				ifd.addField(jpegIFOffset);
			} catch (EOFException ex) {;};
		}		
		/* Another flavor of the old style JPEG compression type 6 contains separate tables */
		TiffField<?> jpegTable = ifd.removeField(TiffTag.JPEG_DC_TABLES);
		if(jpegTable != null) {
			try {
				ifd.addField(copyJPEGHufTable(rin, rout, jpegTable, (int)rout.getStreamPointer()));
			} catch(EOFException ex) {;}
		}
		
		jpegTable = ifd.removeField(TiffTag.JPEG_AC_TABLES);
		if(jpegTable != null) {
			try {
				ifd.addField(copyJPEGHufTable(rin, rout, jpegTable, (int)rout.getStreamPointer()));
			} catch(EOFException ex) {;}
		}
	
		jpegTable = ifd.removeField(TiffTag.JPEG_Q_TABLES);
		if(jpegTable != null) {
			try {
				ifd.addField(copyJPEGQTable(rin, rout, jpegTable, (int)rout.getStreamPointer()));
			} catch(EOFException ex) {;}
		}
		/* End of code to work with old-style JPEG compression */
		
		// Return the actual stream position (we may have lost track of it)  
		return (int)rout.getStreamPointer();	
	}
	
	// Copy a list of IFD and associated image data if any
	private static int copyPages(List<IFD> list, int writeOffset, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		// Write the first page data
		writeOffset = copyPageData(list.get(0), writeOffset, rin, rout);
		// Then write the first IFD
		writeOffset = list.get(0).write(rout, writeOffset);
		// We are going to write the remaining image pages and IFDs if any
		for(int i = 1; i < list.size(); i++) {
			writeOffset = copyPageData(list.get(i), writeOffset, rin, rout);
			// Tell the IFD to update next IFD offset for the following IFD
			list.get(i-1).setNextIFDOffset(rout, writeOffset); 
			writeOffset = list.get(i).write(rout, writeOffset);
		}
		
		return writeOffset;
	}
	
	/**
	 * Extracts ICC_Profile from certain page of TIFF if any
	 * 
	 * @param pageNumber page number from which to extract ICC_Profile
	 * @param rin RandomAccessInputStream for the input TIFF
	 * @return a byte array for the extracted ICC_Profile or null if none exists
	 * @throws Exception
	 */
	public static byte[] extractICCProfile(int pageNumber, RandomAccessInputStream rin) throws Exception {
		// Read pass image header
		int offset = readHeader(rin);
		// Read the IFDs into a list first
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
		
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD workingPage = ifds.get(pageNumber);
		TiffField<?> f_iccProfile = workingPage.getField(TiffTag.ICC_PROFILE);
		if(f_iccProfile != null) {
			return (byte[])f_iccProfile.getData();
		}
		
		return null;
	}
	
	public static byte[] extractICCProfile(RandomAccessInputStream rin) throws Exception {
		return extractICCProfile(0, rin);
	}
	
	public static IRBThumbnail extractThumbnail(int pageNumber, RandomAccessInputStream rin) throws IOException {
		// Read pass image header
		int offset = readHeader(rin);
		// Read the IFDs into a list first
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
		
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD workingPage = ifds.get(pageNumber);
		TiffField<?> f_photoshop = workingPage.getField(TiffTag.PHOTOSHOP);
		if(f_photoshop != null) {
			byte[] data = (byte[])f_photoshop.getData();
			IRBReader reader = new IRBReader(data);
			reader.read();
			if(reader.containsThumbnail()) {
				IRBThumbnail thumbnail = reader.getThumbnail();
				return thumbnail;					
			}		
		}
		
		return null;
	}
	
	public static IRBThumbnail extractThumbnail(RandomAccessInputStream rin) throws IOException {
		return extractThumbnail(0, rin);
	}
	
	public static void extractThumbnail(RandomAccessInputStream rin, String pathToThumbnail) throws IOException {
		IRBThumbnail thumbnail = extractThumbnail(rin);				
		if(thumbnail != null) {
			String outpath = "";
			if(pathToThumbnail.endsWith("\\") || pathToThumbnail.endsWith("/"))
				outpath = pathToThumbnail + "photoshop_thumbnail.jpg";
			else
				outpath = pathToThumbnail.replaceFirst("[.][^.]+$", "") + "_photoshop_t.jpg";
			FileOutputStream fout = new FileOutputStream(outpath);
			if(thumbnail.getDataType() == IRBThumbnail.DATA_TYPE_KJpegRGB) {
				fout.write(thumbnail.getCompressedImage());
			} else {
				ImageWriter writer = ImageIO.getWriter(ImageType.JPG);
				try {
					writer.write(thumbnail.getRawImage(), fout);
				} catch (Exception e) {
					throw new IOException("Writing thumbnail failed!");
				}
			}
			fout.close();	
		}			
	}
	
	// Used to calculate how many bytes to read in case we have only one strip or tile
	private static int[] getBytes2Read(IFD ifd) {
		// Let's calculate how many bytes we are supposed to read
		TiffField<?> tiffField = ifd.getField(TiffTag.IMAGE_WIDTH);
		int imageWidth = tiffField.getDataAsLong()[0];
		tiffField = ifd.getField(TiffTag.IMAGE_LENGTH);
		int imageHeight = tiffField.getDataAsLong()[0];
		
		// For YCbCr image only
		int horizontalSampleFactor = 2; // Default 2X2
		int verticalSampleFactor = 2; // Not 1X1
		
		int photoMetric = ifd.getField(TiffTag.PHOTOMETRIC_INTERPRETATION).getDataAsLong()[0];
		
		// Correction for imageWidth and imageHeight for YCbCr image
		if(photoMetric == TiffFieldEnum.PhotoMetric.YCbCr.getValue()) {
			TiffField<?> f_YCbCrSubSampling = ifd.getField(TiffTag.YCbCr_SUB_SAMPLING);
			
			if(f_YCbCrSubSampling != null) {
				int[] sampleFactors = f_YCbCrSubSampling.getDataAsLong();
				horizontalSampleFactor = sampleFactors[0];
				verticalSampleFactor = sampleFactors[1];
			}
			imageWidth = ((imageWidth + horizontalSampleFactor - 1)/horizontalSampleFactor)*horizontalSampleFactor;
			imageHeight = ((imageHeight + verticalSampleFactor - 1)/verticalSampleFactor)*verticalSampleFactor;	
		}
		
		int samplesPerPixel = 1;
		
		tiffField = ifd.getField(TiffTag.SAMPLES_PER_PIXEL);
		if(tiffField != null) {
			samplesPerPixel = tiffField.getDataAsLong()[0];
		}				
		
		int bitsPerSample = 1;
		
		tiffField = ifd.getField(TiffTag.BITS_PER_SAMPLE);
		if(tiffField != null) {
			bitsPerSample = tiffField.getDataAsLong()[0];
		}
		
		int tileWidth = -1;
		int tileLength = -1;			
		
		TiffField<?> f_tileLength = ifd.getField(TiffTag.TILE_LENGTH);
		TiffField<?> f_tileWidth = ifd.getField(TiffTag.TILE_WIDTH);
		
		if(f_tileWidth != null) {
			tileWidth = f_tileWidth.getDataAsLong()[0];
			tileLength = f_tileLength.getDataAsLong()[0];
		}
		
		int rowsPerStrip = imageHeight;
		int rowWidth = imageWidth;
		
		TiffField<?> f_rowsPerStrip = ifd.getField(TiffTag.ROWS_PER_STRIP);
		if(f_rowsPerStrip != null) rowsPerStrip = f_rowsPerStrip.getDataAsLong()[0];					
		
		if(rowsPerStrip > imageHeight) rowsPerStrip = imageHeight;
		
		if(tileWidth > 0) {
			rowsPerStrip = tileLength;
			rowWidth = tileWidth;
		}
	
		int planaryConfiguration = 1;
		
		tiffField = ifd.getField(TiffTag.PLANAR_CONFIGURATTION);
		if(tiffField != null) planaryConfiguration = tiffField.getDataAsLong()[0];
		
		int[] totalBytes2Read = new int[samplesPerPixel];		
		
		if(planaryConfiguration == 1)
			totalBytes2Read[0] = ((rowWidth*bitsPerSample*samplesPerPixel + 7)/8)*rowsPerStrip;
		else
			totalBytes2Read[0] = totalBytes2Read[1] = totalBytes2Read[2] = ((rowWidth*bitsPerSample + 7)/8)*rowsPerStrip;
		
		if(photoMetric == TiffFieldEnum.PhotoMetric.YCbCr.getValue()) {
			if(samplesPerPixel != 3) samplesPerPixel = 3;
			
			int[] sampleBytesPerRow = new int[samplesPerPixel];
			sampleBytesPerRow[0] = (bitsPerSample*rowWidth + 7)/8;
			sampleBytesPerRow[1] = (bitsPerSample*rowWidth/horizontalSampleFactor + 7)/8;
			sampleBytesPerRow[2] = sampleBytesPerRow[1];
			
			int[] sampleRowsPerStrip = new int[samplesPerPixel];
			sampleRowsPerStrip[0] = rowsPerStrip;
			sampleRowsPerStrip[1] = rowsPerStrip/verticalSampleFactor;
			sampleRowsPerStrip[2]= sampleRowsPerStrip[1];
			
			totalBytes2Read[0] = sampleBytesPerRow[0]*sampleRowsPerStrip[0];
			totalBytes2Read[1] = sampleBytesPerRow[1]*sampleRowsPerStrip[1];
			totalBytes2Read[2] = totalBytes2Read[1];
		
			if(tiffField != null) planaryConfiguration = tiffField.getDataAsLong()[0];
		
			if(planaryConfiguration == 1)
				totalBytes2Read[0] = totalBytes2Read[0] + totalBytes2Read[1] + totalBytes2Read[2];			
		}
		
		return totalBytes2Read;
	}
	
	public static void insertExif(RandomAccessInputStream rin, RandomAccessOutputStream rout, Exif exif, boolean update) throws IOException {
		insertExif(rin, rout, exif, 0, update);
	}
	
	/**
	 * Insert EXIF data with optional thumbnail IFD
	 * 
	 * @param rin input image stream
	 * @param rout output image stream
	 * @param exif EXIF wrapper instance
	 * @param pageNumber page offset where to insert EXIF (zero based)
	 * @param update True to keep the original data, otherwise false
	 * @throws Exception
	 */
	public static void insertExif(RandomAccessInputStream rin, RandomAccessOutputStream rout, Exif exif, int pageNumber, boolean update) throws IOException {
		int offset = copyHeader(rin, rout);
		// Read the IFDs into a list first
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
		
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD imageIFD = ifds.get(pageNumber);
		IFD exifSubIFD = imageIFD.getChild(TiffTag.EXIF_SUB_IFD);
		IFD gpsSubIFD = imageIFD.getChild(TiffTag.GPS_SUB_IFD);
		IFD newImageIFD = exif.getImageIFD();
		IFD newExifSubIFD = exif.getExifIFD();
		IFD newGpsSubIFD = exif.getGPSIFD();
		
		if(newImageIFD != null) { // Copy the Image IFD fields - this is dangerous.
			imageIFD.addFields(newImageIFD.getFields());
		}
		
		if(update && exifSubIFD != null && newExifSubIFD != null) {
			exifSubIFD.addFields(newExifSubIFD.getFields());
			newExifSubIFD = exifSubIFD;
		}
		
		if(newExifSubIFD != null) {
			imageIFD.addField(new LongField(TiffTag.EXIF_SUB_IFD.getValue(), new int[]{0})); // Place holder
			imageIFD.addChild(TiffTag.EXIF_SUB_IFD, newExifSubIFD);		
		}
		
		if(update && gpsSubIFD != null && newGpsSubIFD != null) {
			gpsSubIFD.addFields(newGpsSubIFD.getFields());
			newGpsSubIFD = gpsSubIFD;
		}
		
		if(newGpsSubIFD != null) {
			imageIFD.addField(new LongField(TiffTag.GPS_SUB_IFD.getValue(), new int[]{0})); // Place holder
			imageIFD.addChild(TiffTag.GPS_SUB_IFD, newGpsSubIFD);		
		}
		
		int writeOffset = FIRST_WRITE_OFFSET;
		// Copy pages
		writeOffset = copyPages(ifds, writeOffset, rin, rout);
		int firstIFDOffset = ifds.get(0).getStartOffset();

		writeToStream(rout, firstIFDOffset);
	}
	
	/**
	 * Insert ICC_Profile into TIFF page
	 * 
	 * @param icc_profile byte array holding the ICC_Profile
	 * @param pageNumber page offset where to insert ICC_Profile
	 * @param rin RandomAccessInputStream for the input image
	 * @param rout RandomAccessOutputStream for the output image
	 * @throws Exception
	 */
	public static void insertICCProfile(byte[] icc_profile, int pageNumber, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		int offset = copyHeader(rin, rout);
		// Read the IFDs into a list first
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
		
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD workingPage = ifds.get(pageNumber);
		workingPage.addField(new UndefinedField(TiffTag.ICC_PROFILE.getValue(), icc_profile));
		
		offset = copyPages(ifds, offset, rin, rout);
		int firstIFDOffset = ifds.get(0).getStartOffset();	

		writeToStream(rout, firstIFDOffset);	
	}
	
	public static void insertICCProfile(ICC_Profile icc_profile, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		insertICCProfile(icc_profile.getData(), 0, rin, rout);
	}
	
	/**
	 * Insert ICC_Profile into TIFF page
	 * 
	 * @param icc_profile ICC_Profile
	 * @param pageNumber page number to insert the ICC_Profile
	 * @param rin RandomAccessInputStream for the input image
	 * @param rout RandomAccessOutputStream for the output image
	 * @throws Exception
	 */
	public static void insertICCProfile(ICC_Profile icc_profile, int pageNumber, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		insertICCProfile(icc_profile.getData(), pageNumber, rin, rout);
	}
	
	public static void insertIPTC(RandomAccessInputStream rin, RandomAccessOutputStream rout, List<IPTCDataSet> iptcs, boolean update) throws IOException {
		insertIPTC(rin, rout, 0, iptcs, update);
	}
	
	/**
	 * Insert IPTC data into TIFF image. If the original TIFF image contains IPTC data, we either keep
	 * or override them depending on the input parameter "update."
	 * <p>
	 * There is a possibility that IPTC data presents in more than one places such as a normal TIFF
	 * tag, or buried inside a Photoshop IPTC-NAA Image Resource Block (IRB), or even in a XMP block.
	 * Currently this method does the following thing: if no IPTC data was found from both Photoshop or 
	 * normal IPTC tag, we insert the IPTC data with a normal IPTC tag. If IPTC data is found both as
	 * a Photosho tag and a normal IPTC tag, depending on the "update" parameter, we will either delete
	 * the IPTC data from both places and insert the new IPTC data into the Photoshop tag or we will
	 * synchronize the two sets of IPTC data, delete the original IPTC from both places and insert the
	 * synchronized IPTC data along with the new IPTC data into the Photoshop tag. In both cases, we
	 * will keep the other IRBs from the original Photoshop tag unchanged. 
	 * 
	 * @param rin RandomAccessInputStream for the original TIFF
	 * @param rout RandomAccessOutputStream for the output TIFF with IPTC inserted
	 * @param pageNumber page offset where to insert IPTC
	 * @param iptcs A list of IPTCDataSet to insert into the TIFF image
	 * @param update whether we want to keep the original image or create a completely new IPTC data set
	 * @throws IOException
	 */
	public static void insertIPTC(RandomAccessInputStream rin, RandomAccessOutputStream rout, int pageNumber, List<IPTCDataSet> iptcs, boolean update) throws IOException {
		int offset = copyHeader(rin, rout);
		// Read the IFDs into a list first
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
		
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD workingPage = ifds.get(pageNumber);
	
		ByteArrayOutputStream bout = new ByteArrayOutputStream();
		
		// See if we also have regular IPTC tag field
		TiffField<?> f_iptc = workingPage.removeField(TiffTag.IPTC);		
		TiffField<?> f_photoshop = workingPage.getField(TiffTag.PHOTOSHOP);
		if(f_photoshop != null) { // Read 8BIMs
			IRB irb = new IRB((byte[])f_photoshop.getData());
			// Shallow copy the map.
			Map<Short, _8BIM> bims = new HashMap<Short, _8BIM>(irb.get8BIM());
			_8BIM photoshop_iptc = bims.remove(ImageResourceID.IPTC_NAA.getValue());
			if(photoshop_iptc != null) { // If we have IPTC
				if(update) { // If we need to keep the old data, copy it
					if(f_iptc != null) {// We are going to synchronize the two IPTC data
						byte[] data = null;
						if(f_iptc.getType() == FieldType.LONG)
							data = ArrayUtils.toByteArray(f_iptc.getDataAsLong(), rin.getEndian() == IOUtils.BIG_ENDIAN);
						else
							data = (byte[])f_iptc.getData();
						copyIPTCDataSet(iptcs, data);
					}
					// Now copy the Photoshop IPTC data
					copyIPTCDataSet(iptcs, photoshop_iptc.getData());
					// Remove duplicates
					iptcs = new ArrayList<IPTCDataSet>(new HashSet<IPTCDataSet>(iptcs));
				}
			}
			// Create IPTC 8BIM
			for(IPTCDataSet dataset : iptcs) {
				dataset.write(bout);
			}
			_8BIM iptc_bim = new _8BIM(ImageResourceID.IPTC_NAA, "iptc", bout.toByteArray());
			bout.reset();
			iptc_bim.write(bout); // Write the IPTC 8BIM first
			for(_8BIM bim : bims.values()) // Copy the other 8BIMs if any
				bim.write(bout);
			// Add a new Photoshop tag field to TIFF
			workingPage.addField(new UndefinedField(TiffTag.PHOTOSHOP.getValue(), bout.toByteArray()));
		} else { // We don't have photoshop, add IPTC to regular IPTC tag field
			if(f_iptc != null && update) {
				byte[] data = null;
				if(f_iptc.getType() == FieldType.LONG)
					data = ArrayUtils.toByteArray(f_iptc.getDataAsLong(), rin.getEndian() == IOUtils.BIG_ENDIAN);
				else
					data = (byte[])f_iptc.getData();
				copyIPTCDataSet(iptcs, data);
			}
			for(IPTCDataSet dataset : iptcs) {
				dataset.write(bout);
			}		
			workingPage.addField(new UndefinedField(TiffTag.IPTC.getValue(), bout.toByteArray()));
		}		
		
		offset = copyPages(ifds, offset, rin, rout);
		int firstIFDOffset = ifds.get(0).getStartOffset();	

		writeToStream(rout, firstIFDOffset);	
	}
	
	public static void insertIRB(RandomAccessInputStream rin, RandomAccessOutputStream rout, List<_8BIM> bims, boolean update) throws IOException {
		insertIRB(rin, rout, 0, bims, update);
	}
	
	public static void insertIRB(RandomAccessInputStream rin, RandomAccessOutputStream rout, int pageNumber, List<_8BIM> bims, boolean update) throws IOException {
		int offset = copyHeader(rin, rout);
		// Read the IFDs into a list first
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
	
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD workingPage = ifds.get(pageNumber);
		
		ByteArrayOutputStream bout = new ByteArrayOutputStream();
		
		if(update) {
			TiffField<?> f_irb = workingPage.getField(TiffTag.PHOTOSHOP);
			if(f_irb != null) {
				IRB irb = new IRB((byte[])f_irb.getData());
				// Shallow copy the map
				Map<Short, _8BIM> bimMap = new HashMap<Short, _8BIM>(irb.get8BIM());
				for(_8BIM bim : bims)
					bimMap.remove(bim.getID());
				bims.addAll(bimMap.values());
			}
		}
		
		for(_8BIM bim : bims)
			bim.write(bout);
		
		workingPage.addField(new UndefinedField(TiffTag.PHOTOSHOP.getValue(), bout.toByteArray()));
		
		offset = copyPages(ifds, offset, rin, rout);
		int firstIFDOffset = ifds.get(0).getStartOffset();	

		writeToStream(rout, firstIFDOffset);	
	}
	
	/**
	 * Insert a thumbnail into PHOTOSHOP private tag field
	 *  
	 * @param rin RandomAccessInputStream for the input TIFF
	 * @param rout RandomAccessOutputStream for the output TIFF
	 * @param thumbnail a BufferedImage to be inserted
	 * @throws Exception
	 */
	public static void insertThumbnail(RandomAccessInputStream rin, RandomAccessOutputStream rout, BufferedImage thumbnail) throws IOException {
		// Sanity check
		if(thumbnail == null) throw new IllegalArgumentException("Input thumbnail is null");
		insertIRB(rin, rout, Arrays.asList(MetadataUtils.createThumbnail8BIM(thumbnail)), true);
	}
	
	public static void insertXMP(byte[] xmp, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		insertXMP(xmp, 0, rin, rout);
	}
	
	/**
	 * Insert XMP data into TIFF image
	 * @param xmp byte array for the XMP data to be inserted
	 * @param pageNumber page offset where to insert XMP
	 * @param rin RandomAccessInputStream for the input image
	 * @param rout RandomAccessOutputStream for the output image
	 * @throws IOException
	 */
	public static void insertXMP(byte[] xmp, int pageNumber, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		int offset = copyHeader(rin, rout);
		// Read the IFDs into a list first
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
		
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD workingPage = ifds.get(pageNumber);
		workingPage.addField(new UndefinedField(TiffTag.XMP.getValue(), xmp));
		
		offset = copyPages(ifds, offset, rin, rout);
		int firstIFDOffset = ifds.get(0).getStartOffset();	

		writeToStream(rout, firstIFDOffset);	
	}
	
	public static void insertXMP(String xmp, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		Document doc = XMLUtils.createXML(xmp);
		XMLUtils.insertLeadingPI(doc, "xpacket", "begin='' id='W5M0MpCehiHzreSzNTczkc9d'");
		XMLUtils.insertTrailingPI(doc, "xpacket", "end='w'");
		byte[] xmpBytes = XMLUtils.serializeToByteArray(doc);
		insertXMP(xmpBytes, rin, rout);
	}
	
	public static void printIFDs(Collection<IFD> list, String indent) {
		int id = 0;
		System.out.print(indent);
		for(IFD currIFD : list) {
			System.out.println("IFD #" + id);
			printIFD(currIFD, TiffTag.class, indent);
			id++;
		}
	}
	
	public static void printIFD(IFD currIFD, Class<? extends Tag> tagClass, String indent) {
		// Use reflection to invoke fromShort(short) method
		Method method = null;
		try {
			method = tagClass.getDeclaredMethod("fromShort", short.class);
		} catch (NoSuchMethodException e) {
			e.printStackTrace();
		} catch (SecurityException e) {
			e.printStackTrace();
		}
		Collection<TiffField<?>> fields = currIFD.getFields();
		int i = 0;
		for(TiffField<?> field : fields) {
			System.out.print(indent);
			System.out.println("Field #" + i);
			System.out.print(indent);
			short tag = field.getTag();
			Tag ftag = TiffTag.UNKNOWN;
			try {
				ftag = (Tag)method.invoke(null, tag);
			} catch (IllegalAccessException e) {
				e.printStackTrace();
			} catch (IllegalArgumentException e) {
				e.printStackTrace();
			} catch (InvocationTargetException e) {
				e.printStackTrace();
			}
			if (ftag == TiffTag.UNKNOWN) {
				System.out.println("Tag: " + ftag + " [Value: 0x"+ Integer.toHexString(tag&0xffff) + "]" + " (Unknown)");
			} else {
				System.out.println("Tag: " + ftag);
			}
			FieldType ftype = field.getType();				
			System.out.print(indent);
			System.out.println("Field type: " + ftype);
			int field_length = field.getLength();
			System.out.print(indent);
			System.out.println("Field length: " + field_length);
			System.out.print(indent);			
			
			String suffix = null;
			if(ftype == FieldType.SHORT || ftype == FieldType.SSHORT)
				suffix = ftag.getFieldAsString(field.getDataAsLong());
			else
				suffix = ftag.getFieldAsString(field.getData());			
			
			System.out.println("Field value: " + field.getDataAsString() + (StringUtils.isNullOrEmpty(suffix)?"":" => " + suffix));
			
			i++;
		}
		
		Map<Tag, IFD> children = currIFD.getChildren();
		
		if(children.get(TiffTag.EXIF_SUB_IFD) != null) {
			System.out.print(indent + "--------- ");
			System.out.println("<<Exif SubIFD starts>>");
			printIFD(children.get(TiffTag.EXIF_SUB_IFD), ExifTag.class, indent + "--------- ");
			System.out.print(indent + "--------- ");
			System.out.println("<<Exif SubIFD ends>>");
		}
		
		if(children.get(TiffTag.GPS_SUB_IFD) != null) {
			System.out.print(indent + "--------- ");
			System.out.println("<<GPS SubIFD starts>>");
			printIFD(children.get(TiffTag.GPS_SUB_IFD), GPSTag.class, indent + "--------- ");
			System.out.print(indent + "--------- ");
			System.out.println("<<GPS SubIFD ends>>");
		}		
	}
	
	private static int readHeader(RandomAccessInputStream rin) throws IOException {
		int offset = 0;
	    // First 2 bytes determine the byte order of the file
		rin.seek(STREAM_HEAD);
	    short endian = rin.readShort();
	    offset += 2;
	
		if (endian == IOUtils.BIG_ENDIAN)
		{
		    System.out.println("Byte order: Motorola BIG_ENDIAN");
		    rin.setReadStrategy(ReadStrategyMM.getInstance());
		}
		else if(endian == IOUtils.LITTLE_ENDIAN)
		{
		    System.out.println("Byte order: Intel LITTLE_ENDIAN");
		    rin.setReadStrategy(ReadStrategyII.getInstance());
		}
		else {		
			rin.close();
			throw new RuntimeException("Invalid TIFF byte order");
	    }
		
		// Read TIFF identifier
		rin.seek(offset);
		short tiff_id = rin.readShort();
		offset +=2;
		if(tiff_id!=0x2a)//"*" 42 decimal
		{
			rin.close();
			throw new RuntimeException("Invalid TIFF identifier");
		}
		
		rin.seek(offset);
		offset = rin.readInt();
			
		return offset;
	}
	
	private static int readIFD(IFD parent, Tag parentTag, Class<? extends Tag> tagClass, RandomAccessInputStream rin, List<IFD> list, int offset, String indent) throws IOException 
	{	
		// Use reflection to invoke fromShort(short) method
		Method method = null;
		try {
			method = tagClass.getDeclaredMethod("fromShort", short.class);
		} catch (NoSuchMethodException e) {
			e.printStackTrace();
		} catch (SecurityException e) {
			e.printStackTrace();
		}
		String indent2 = indent + "----- "; // Increment indentation
		IFD tiffIFD = new IFD();
		rin.seek(offset);
		int no_of_fields = rin.readShort();
		System.out.print(indent);
		System.out.println("Total number of fields: " + no_of_fields);
		offset += 2;
		
		for (int i = 0; i < no_of_fields; i++)
		{
			System.out.print(indent);
			System.out.println("Field "+i+" =>");
			rin.seek(offset);
			short tag = rin.readShort();
			Tag ftag = TiffTag.UNKNOWN;
			try {
				ftag = (Tag)method.invoke(null, tag);
			} catch (IllegalAccessException e) {
				e.printStackTrace();
			} catch (IllegalArgumentException e) {
				e.printStackTrace();
			} catch (InvocationTargetException e) {
				e.printStackTrace();
			}
			System.out.print(indent);
			if (ftag == TiffTag.UNKNOWN) {
				System.out.println("Tag: " + ftag + " [Value: 0x"+ Integer.toHexString(tag&0xffff) + "]" + " (Unknown)");
			} else {
				System.out.println("Tag: " + ftag);
			}
			offset += 2;
			rin.seek(offset);
			short type = rin.readShort();
			FieldType ftype = FieldType.fromShort(type);
			System.out.print(indent);
			System.out.println("Data type: " + ftype);
			offset += 2;
			rin.seek(offset);
			int field_length = rin.readInt();
			System.out.print(indent);
			System.out.println("Field length: " + field_length);
			offset += 4;
			String suffix = null;
			////// Try to read actual data.
			switch (ftype)
			{
				case BYTE:
				case UNDEFINED:
					byte[] data = new byte[field_length];
					rin.seek(offset);
					if(field_length <= 4) {						
						rin.readFully(data, 0, field_length);					   
					} else {
						rin.seek(rin.readInt());
						rin.readFully(data, 0, field_length);
					}					
					TiffField<byte[]> byteField = null;
					if(ftype == FieldType.BYTE)
						byteField = new ByteField(tag, data);
					else
						byteField = new UndefinedField(tag, data);
					tiffIFD.addField(byteField);
					System.out.print(indent);
					if(ftag == TiffTag.ICC_PROFILE) {
						showICCProfile(data);
					} else if(ftag == TiffTag.PHOTOSHOP) {
						showPhtoshop(data);
					} else if(ftag == TiffTag.XMP) {						
						XMLUtils.showXML(XMLUtils.createXML(data));
					} else if(ftag == TiffTag.IPTC) {
						showIPTC(data);
					}
					suffix = ftag.getFieldAsString(data);
					System.out.println("Field value: " + byteField.getDataAsString() + (StringUtils.isNullOrEmpty(suffix)?"":" => " + suffix));
					offset += 4;					
					break;
				case ASCII:
					data = new byte[field_length];
					if(field_length <= 4) {
						rin.seek(offset);
						rin.readFully(data, 0, field_length);
					}						
					else {
						rin.seek(offset);
						rin.seek(rin.readInt());
						rin.readFully(data, 0, field_length);
					}
					TiffField<String> ascIIField = new ASCIIField(tag, new String(data, 0, data.length, "UTF-8"));
					tiffIFD.addField(ascIIField);
					if(data.length>0) {
						System.out.print(indent);
						System.out.println("Field value: " + ascIIField.getDataAsString());
					}
					offset += 4;	
					break;
				case SHORT:
					short[] sdata = new short[field_length];
					if(field_length == 1) {
					  rin.seek(offset);
					  sdata[0] = rin.readShort();
					  offset += 4;
					}
					else if (field_length == 2)
					{
						rin.seek(offset);
						sdata[0] = rin.readShort();
						offset += 2;
						rin.seek(offset);
						sdata[1] = rin.readShort();
						offset += 2;
					}
					else {
						rin.seek(offset);
						int toOffset = rin.readInt();
						offset += 4;
						for (int j = 0; j  <field_length; j++){
							rin.seek(toOffset);
							sdata[j] = rin.readShort();
							toOffset += 2;
						}
					}
					TiffField<short[]> shortField = new ShortField(tag, sdata);
					tiffIFD.addField(shortField);
					System.out.print(indent);
					suffix = ftag.getFieldAsString(shortField.getDataAsLong());
					System.out.println("Field value: " + shortField.getDataAsString() + (StringUtils.isNullOrEmpty(suffix)?"":" => " + suffix));
					break;
				case LONG:
					int[] ldata = new int[field_length];
					if(field_length == 1) {
					  rin.seek(offset);
					  ldata[0] = rin.readInt();
					  offset += 4;
					}
					else {
						rin.seek(offset);
						int toOffset = rin.readInt();
						offset += 4;
						for (int j=0;j<field_length; j++){
							rin.seek(toOffset);
							ldata[j] = rin.readInt();
							toOffset += 4;
						}
					}
					TiffField<int[]> longField = new LongField(tag, ldata);
					tiffIFD.addField(longField);
					
					System.out.print(indent);
					suffix = ftag.getFieldAsString(ldata);
					System.out.println("Field value: " + longField.getDataAsString() + (StringUtils.isNullOrEmpty(suffix)?"":" => " + suffix));
					
					if ((ftag == TiffTag.EXIF_SUB_IFD) && (ldata[0]!= 0)) {
						System.out.print(indent);
						System.out.println("<<ExifSubIFD: offset byte " + offset + ">>");
						try { // If something bad happens, we skip the sub IFD
							readIFD(tiffIFD, TiffTag.EXIF_SUB_IFD, ExifTag.class, rin, null, ldata[0], indent2);
						} catch(Exception e) {
							tiffIFD.removeField(TiffTag.EXIF_SUB_IFD);
							e.printStackTrace();
						}
					} else if ((ftag == TiffTag.GPS_SUB_IFD) && (ldata[0] != 0)) {
						System.out.print(indent);
						System.out.println("<<GPSSubIFD: offset byte " + offset + ">>");
						try {
							readIFD(tiffIFD, TiffTag.GPS_SUB_IFD, GPSTag.class, rin, null, ldata[0], indent2);
						} catch(Exception e) {
							tiffIFD.removeField(TiffTag.GPS_SUB_IFD);
							e.printStackTrace();
						}
					} else if((ftag == ExifTag.EXIF_INTEROPERABILITY_OFFSET) && (ldata[0] != 0)) {
						System.out.print(indent);
						System.out.println("<<ExifInteropSubIFD: offset byte " + offset + ">>");
						try {
							readIFD(tiffIFD, ExifTag.EXIF_INTEROPERABILITY_OFFSET, InteropTag.class, rin, null, ldata[0], indent2);
						} catch(Exception e) {
							tiffIFD.removeField(ExifTag.EXIF_INTEROPERABILITY_OFFSET);
							e.printStackTrace();
						}
					} else if (ftag == TiffTag.IPTC) {
						showIPTC(ArrayUtils.toByteArray(ldata, rin.getEndian() == IOUtils.BIG_ENDIAN));						
					} else if (ftag == TiffTag.SUB_IFDS) {						
						for(int ifd = 0; ifd < ldata.length; ifd++) {
							System.out.print(indent);
							System.out.println("******* SubIFD " + ifd + " *******");
							try {
								readIFD(tiffIFD, TiffTag.SUB_IFDS, TiffTag.class, rin, null, ldata[0], indent2);
							} catch(Exception e) {
								tiffIFD.removeField(TiffTag.SUB_IFDS);
								e.printStackTrace();
							}
							System.out.println("******* End of SubIFD " + ifd + " *******");
						}
					}				
					break;
				case FLOAT:
					float[] fdata = new float[field_length];
					if(field_length == 1) {
					  rin.seek(offset);
					  fdata[0] = rin.readFloat();
					  offset += 4;
					}
					else {
						rin.seek(offset);
						int toOffset = rin.readInt();
						offset += 4;
						for (int j=0;j<field_length; j++){
							rin.seek(toOffset);
							fdata[j] = rin.readFloat();
							toOffset += 4;
						}
					}
					TiffField<float[]> floatField = new FloatField(tag, fdata);
					tiffIFD.addField(floatField);
					
					System.out.print(indent);
					System.out.println("Field value: " + floatField.getDataAsString());
						
					break;
				case DOUBLE:
					double[] ddata = new double[field_length];
					rin.seek(offset);
					int toOffset = rin.readInt();
					offset += 4;
					for (int j=0;j<field_length; j++){
						rin.seek(toOffset);
						ddata[j] = rin.readDouble();
						toOffset += 8;
					}
					TiffField<double[]> doubleField = new DoubleField(tag, ddata);
					tiffIFD.addField(doubleField);
					
					System.out.print(indent);
					System.out.println("Field value: " + doubleField.getDataAsString());
						
					break;
				case RATIONAL:
				case SRATIONAL:
					int len = 2*field_length;
					ldata = new int[len];	
					rin.seek(offset);
					toOffset = rin.readInt();
					offset += 4;					
					for (int j=0;j<len; j+=2){
						rin.seek(toOffset);
						ldata[j] = rin.readInt();
						toOffset += 4;
						rin.seek(toOffset);
						ldata[j+1] = rin.readInt();
						toOffset += 4;
					}
					TiffField<int[]> rationalField = null;
					if(ftype == FieldType.SRATIONAL) {
						rationalField = new SRationalField(tag, ldata);
					} else {
						rationalField = new RationalField(tag, ldata);
					}
					System.out.print(indent);
					suffix = ftag.getFieldAsString(ldata);
					System.out.println("Field value: " + rationalField.getDataAsString() + (StringUtils.isNullOrEmpty(suffix)?"":" => " + suffix));
					tiffIFD.addField(rationalField);
					
					break;
				case IFD:
					ldata = new int[field_length];
					if(field_length == 1) {
					  rin.seek(offset);
					  ldata[0] = rin.readInt();
					  offset += 4;
					}
					else {
						rin.seek(offset);
						toOffset = rin.readInt();
						offset += 4;
						for (int j=0;j<field_length; j++){
							rin.seek(toOffset);
							ldata[j] = rin.readInt();
							toOffset += 4;
						}
					}
					TiffField<int[]> ifdField = new IFDField(tag, ldata);
					tiffIFD.addField(ifdField);
					System.out.print(indent);
					suffix = ftag.getFieldAsString(ldata);
					System.out.println("Field value: " + ifdField.getDataAsString() + (StringUtils.isNullOrEmpty(suffix)?"":" => " + suffix));
					for(int ifd = 0; ifd < ldata.length; ifd++) {
						System.out.print(indent);
						System.out.println("******* SubIFD " + ifd + " *******");
						readIFD(tiffIFD, TiffTag.SUB_IFDS, TiffTag.class, rin, null, ldata[0], indent2);
						System.out.println("******* End of SubIFD " + ifd + " *******");
					}
								
					break;
				default:
					offset += 4;
					break;					
			}
		}
		// If this is a child IFD, add it to its parent
		if(parent != null)
			parent.addChild(parentTag, tiffIFD);
		else // Otherwise, add to the main IFD list
			list.add(tiffIFD);
		rin.seek(offset);
		
		return rin.readInt();
	}
	
	private static void readIFDs(IFD parent, Tag parentTag, Class<? extends Tag> tagClass, List<IFD> list, int offset, RandomAccessInputStream rin) throws IOException {
		int ifd = 0;
		// Read the IFDs into a list first	
		while (offset != 0)
		{
			System.out.println("************************************************");
			System.out.println("IFD " + ifd++ + " => offset byte " + offset);
			offset = readIFD(parent, parentTag, tagClass, rin, list, offset, "");
		}
	}
	
	public static void readIFDs(List<IFD> list, RandomAccessInputStream rin) throws IOException {
		int offset = readHeader(rin);
		readIFDs(null, null, TiffTag.class, list, offset, rin);
	}
	
	public static Map<MetadataType, Metadata> readMetadata(RandomAccessInputStream rin) throws IOException {
		return readMetadata(rin, 0);
	}
	
	public static Map<MetadataType, Metadata> readMetadata(RandomAccessInputStream rin, int pageNumber) throws IOException	{
		Map<MetadataType, Metadata> metadataMap = new HashMap<MetadataType, Metadata>();
		System.out.println("*** TIFF snooping starts ***");
		int offset = readHeader(rin);
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
		
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD currIFD = ifds.get(pageNumber);
		TiffField<?> field = currIFD.getField(TiffTag.ICC_PROFILE); 
		if(field != null) { // We have found ICC_Profile
			metadataMap.put(MetadataType.ICC_PROFILE, new ICCProfile((byte[])field.getData()));
		}
		field = currIFD.getField(TiffTag.XMP);
		if(field != null) { // We have found XMP
			metadataMap.put(MetadataType.XMP, new XMP((byte[])field.getData()));
		}
		field = currIFD.getField(TiffTag.PHOTOSHOP);
		if(field != null) { // We have found Photoshop IRB
			IRB irb = new IRB((byte[])field.getData());
			metadataMap.put(MetadataType.PHOTOSHOP, irb);
			_8BIM photoshop_8bim = irb.get8BIM(ImageResourceID.IPTC_NAA.getValue());
			if(photoshop_8bim != null) { // If we have IPTC data inside Photoshop, keep it
				IPTC iptc = new IPTC(photoshop_8bim.getData());
				metadataMap.put(MetadataType.IPTC, iptc);
			}
		}
		field = currIFD.getField(TiffTag.IPTC);
		if(field != null) { // We have found IPTC data
			FieldType type = field.getType();
			if(type == FieldType.LONG)
				metadataMap.put(MetadataType.IPTC, new IPTC(ArrayUtils.toByteArray(field.getDataAsLong(), rin.getEndian() == IOUtils.BIG_ENDIAN)));
			else
				metadataMap.put(MetadataType.IPTC, new IPTC((byte[])field.getData()));
		}
		field = currIFD.getField(TiffTag.EXIF_SUB_IFD);
		if(field != null) { // We have found EXIF SubIFD
			metadataMap.put(MetadataType.EXIF, new TiffExif(currIFD));
		}
		
		System.out.println("*** TIFF snooping ends ***");
		
		return metadataMap;
	}
	
	public static void removeMetadata(int pageNumber, RandomAccessInputStream rin, RandomAccessOutputStream rout, MetadataType ... metadataTypes) throws IOException {
		removeMetadata(new HashSet<MetadataType>(Arrays.asList(metadataTypes)), pageNumber, rin, rout);
	}
	
	public static void removeMetadata(RandomAccessInputStream rin, RandomAccessOutputStream rout, MetadataType ... metadataTypes) throws IOException {
		removeMetadata(0, rin, rout, metadataTypes);
	}
	
	/**
	 * Remove meta data from TIFF image
	 * 
	 * @param pageNumber working page from which to remove EXIF and GPS data
	 * @param rin RandomAccessInputStream for the input image
	 * @param rout RandomAccessOutputStream for the output image
	 * @throws IOException
	 */
	public static void removeMetadata(Set<MetadataType> metadataTypes, int pageNumber, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		int offset = copyHeader(rin, rout);
		// Read the IFDs into a list first
		List<IFD> ifds = new ArrayList<IFD>();
		readIFDs(null, null, TiffTag.class, ifds, offset, rin);
	
		if(pageNumber < 0 || pageNumber >= ifds.size())
			throw new IllegalArgumentException("pageNumber " + pageNumber + " out of bounds: 0 - " + (ifds.size() - 1));
		
		IFD workingPage = ifds.get(pageNumber);
		
		TiffField<?> metadata = null;
		
		for(MetadataType metaType : metadataTypes) {
			switch(metaType) {
				case XMP:
					workingPage.removeField(TiffTag.XMP);
					metadata = workingPage.removeField(TiffTag.PHOTOSHOP);
					if(metadata != null) {
						byte[] data = (byte[])metadata.getData();
						// We only remove XMP and keep the other IRB data untouched.
						removeMetadataFromIRB(workingPage, data, ImageResourceID.XMP_METADATA);
					}
					break;
				case IPTC:
					workingPage.removeField(TiffTag.IPTC);
					metadata = workingPage.removeField(TiffTag.PHOTOSHOP);
					if(metadata != null) {
						byte[] data = (byte[])metadata.getData();
						// We only remove IPTC_NAA and keep the other IRB data untouched.
						removeMetadataFromIRB(workingPage, data, ImageResourceID.IPTC_NAA);
					}
					break;
				case ICC_PROFILE:
					workingPage.removeField(TiffTag.ICC_PROFILE);
					metadata = workingPage.removeField(TiffTag.PHOTOSHOP);
					if(metadata != null) {
						byte[] data = (byte[])metadata.getData();
						// We only remove ICC_PROFILE and keep the other IRB data untouched.
						removeMetadataFromIRB(workingPage, data, ImageResourceID.ICC_PROFILE);
					}
					break;
				case PHOTOSHOP:
					workingPage.removeField(TiffTag.PHOTOSHOP);
					break;
				case EXIF:
					workingPage.removeField(TiffTag.EXIF_SUB_IFD);
					workingPage.removeField(TiffTag.GPS_SUB_IFD);
					metadata = workingPage.removeField(TiffTag.PHOTOSHOP);
					if(metadata != null) {
						byte[] data = (byte[])metadata.getData();
						// We only remove EXIF and keep the other IRB data untouched.
						removeMetadataFromIRB(workingPage, data, ImageResourceID.EXIF_DATA1, ImageResourceID.EXIF_DATA3);
					}
					break;
				default:
			}
		}
		
		offset = copyPages(ifds, offset, rin, rout);
		int firstIFDOffset = ifds.get(0).getStartOffset();	

		writeToStream(rout, firstIFDOffset);		
	}
	
	public static void removeMetadata(Set<MetadataType> metadataTypes, RandomAccessInputStream rin, RandomAccessOutputStream rout) throws IOException {
		removeMetadata(metadataTypes, 0, rin, rout);
	}
	
	private static void removeMetadataFromIRB(IFD workingPage, byte[] data, ImageResourceID ... ids) throws IOException {
		IRB irb = new IRB(data);
		// Shallow copy the map.
		Map<Short, _8BIM> bimMap = new HashMap<Short, _8BIM>(irb.get8BIM());								
		// We only remove XMP and keep the other IRB data untouched.
		for(ImageResourceID id : ids)
			bimMap.remove(id.getValue());
		if(bimMap.size() > 0) {
		   	// Write back the IRB
			ByteArrayOutputStream bout = new ByteArrayOutputStream();
			for(_8BIM bim : bimMap.values())
				bim.write(bout);
			// Add new PHOTOSHOP field
			workingPage.addField(new ByteField(TiffTag.PHOTOSHOP.getValue(), bout.toByteArray()));
		}		
	}
		
	private static void showICCProfile(byte[] icc_profile) {
		ICCProfile.showProfile(icc_profile);
	}
	
	private static void showIPTC(byte[] iptc) {
		new IPTCReader(iptc).showMetadata();			
	}
	
	private static void showPhtoshop(byte[] data) {
		new IRBReader(data).showMetadata();		
	}
	
	private static void writeToStream(RandomAccessOutputStream rout, int firstIFDOffset) throws IOException {
		// Go to the place where we should write the first IFD offset
		// and write the first IFD offset
		rout.seek(OFFSET_TO_WRITE_FIRST_IFD_OFFSET);
		rout.writeInt(firstIFDOffset);
		// Dump the data to the real output stream
		rout.seek(STREAM_HEAD);
		rout.writeToStream(rout.getLength());
		//rout.flush();
	}
}