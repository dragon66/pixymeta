/**
 * Copyright (C) 2014-2019 by Wen Yu.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Any modifications to this file must keep this entire header intact.
 */

package pixy.image.tiff;

import pixy.string.StringUtils;

/**
 * TIFF SLong type field.
 * 
 * @author Wen Yu, yuwen_66@yahoo.com
 * @version 1.0 02/24/2013
 */
public final class SLongField extends AbstractLongField {

	public SLongField(short tag, int[] data) {
		super(tag, FieldType.SLONG, data);
	}
	
	public String getDataAsString() {
		return StringUtils.longArrayToString(data, 0,  MAX_STRING_REPR_LEN, false);
	}
}
