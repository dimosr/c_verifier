/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public class FileUtil {
	public static Thread copy(final InputStream in, final OutputStream out) {
		
		Thread thread  = new Thread(new Runnable() {
			
			@Override
			public void run() {
				byte[] buffer = new byte[1024];
				int len;
				try {
					while ((len = in.read(buffer)) != -1) {
						out.write(buffer, 0, len);
					}
				} catch (IOException e) {
				} finally {
					try {
						// these do nothing but oh well
						// - may be needed if changes are made in the future.
						out.flush();
						out.close();
					} catch (IOException e) {
					}
				}
			}
		});
		
		thread.start();
		return thread;
	}
}
