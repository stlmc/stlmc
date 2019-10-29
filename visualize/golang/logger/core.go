package logger

import "log"

var Logger = loggerStruct{}

// Logger type defines logger
type loggerStruct struct {
	// IsDebug is check whether it is on
	// debugging mode or not.
	IsDebug bool
}

func (lo *loggerStruct) Debug(args ...interface{}) {
	if lo.IsDebug {
		lo.Print(args...)
	}
}

func (lo *loggerStruct) Error(args ...interface{}) {
	if lo.IsDebug {
		lo.Print(args...)
	}
}

func (lo *loggerStruct) Print(args ...interface{}) {
	log.Print(args...)
}