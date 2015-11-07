/**
 * Copyright (c) 2014-2015 by Wen Yu.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Any modifications to this file must keep this entire header intact.
 * 
 * Change History - most recent changes go on top of previous changes
 *
 * Comments.java
 *
 * Who   Date       Description
 * ====  =========  =================================================
 * WY    06Nov2015  Initial creation
 */

package pixy.meta.image;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import pixy.meta.Metadata;
import pixy.meta.MetadataType;

public class Comments extends Metadata {
	// Obtain a logger instance
	private static final Logger LOGGER = LoggerFactory.getLogger(Comments.class);
		
	private Queue<byte[]> queue;
	private List<byte[]> rawComments;
	private List<String> comments;
	
	public Comments() {
		super(MetadataType.COMMENT, null);
		queue = new LinkedList<byte[]>();
		rawComments = new ArrayList<byte[]>();
		comments = new ArrayList<String>();
	}
	
	public Comments(List<String> comments) {
		super(MetadataType.COMMENT, null);
		queue = new LinkedList<byte[]>();
		rawComments = new ArrayList<byte[]>();
		if(comments == null) throw new IllegalArgumentException("Input is null");
		this.comments = comments;
	}

	public List<String> getComments() {
		ensureDataRead();
		return Collections.unmodifiableList(comments);
	}
	
	public void addComment(byte[] comment) {
		if(comment == null) throw new IllegalArgumentException("Input is null");
		queue.offer(comment);
	}
	
	public void read() throws IOException {
		if(queue.size() > 0) {
			for(byte[] comment : queue) {
				try {
					comments.add(new String(comment, "UTF-8"));
				} catch (UnsupportedEncodingException e) {
					throw new UnsupportedEncodingException("UTF-8");
				}
				rawComments.add(comment);
			}
			queue.clear();
		}
	}
	
	@Override
	public void showMetadata() {
		ensureDataRead();
		
		LOGGER.info("Comments start =>");
		
		for (String comment : comments)
		    LOGGER.info("Comment: {}", comment);
		
		LOGGER.info("Comments end <=");
	}	
}