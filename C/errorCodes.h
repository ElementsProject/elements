/* This module defines some constants used for error codes when processing Simplicity.
 * Errors can either indicate a transient or a permanent failure.
 */
#ifndef ERRORCODES_H
#define ERRORCODES_H

/* By convention, odd error codes are transient failures (i.e. out of memory or I/O errors)
 * while even error codes are permanent failures (i.e. unexpected end of file or parsing error, etc.)
 */
#define ERR_MALLOC (-1)
#define ERR_BITSTREAM_EOF (-2)
#define ERR_BITSTREAM_ERROR (-3)
#define ERR_DATA_OUT_OF_RANGE (-4)
#define ERR_NOT_YET_IMPLEMENTED (-5)
#define ERR_FAIL_CODE (-6)
#define ERR_STOP_CODE (-8)
#define ERR_HIDDEN (-10)

#define PERMANENT_FAILURE(err) (!((err) & 1))

#endif
