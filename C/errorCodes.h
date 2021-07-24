/* This module defines some constants used for error codes when processing Simplicity.
 * Errors can either indicate a transient or a permanent failure.
 */
#ifndef SIMPLICITY_ERRORCODES_H
#define SIMPLICITY_ERRORCODES_H

/* By convention, odd error codes are transient failures (i.e. out of memory or I/O errors)
 * while even error codes are permanent failures (i.e. unexpected end of file or parsing error, etc.)
 */
#define SIMPLICITY_ERR_MALLOC (-1)
#define SIMPLICITY_ERR_BITSTREAM_EOF (-2)
#define SIMPLICITY_ERR_BITSTREAM_ERROR (-3)
#define SIMPLICITY_ERR_DATA_OUT_OF_RANGE (-4)
#define SIMPLICITY_ERR_NOT_YET_IMPLEMENTED (-5)
#define SIMPLICITY_ERR_DATA_OUT_OF_ORDER (-6)
#define SIMPLICITY_ERR_FAIL_CODE (-8)
#define SIMPLICITY_ERR_STOP_CODE (-10)
#define SIMPLICITY_ERR_HIDDEN (-12)

#define PERMANENT_FAILURE(err) (!((err) & 1))

#endif
