package data

import (
	"golang/logger"
	"io/ioutil"
	"os"
	"path/filepath"
)


var Workspace = workspace{
	DirName: "./DataDir",
}


// workspace represents Workspace dir. DirName is the directory's name
// FileList contains files in directory with inner indexing. SimpleFileList contains
// only file names without indexing. Num holds total number of files in directory.
// isDir checks whether current searching name is directory or file.
type workspace struct {
	DirName string			`json:"dirname"`
	FileList []FileDesc		`json:"file_list"`
	SimpleFileList []string	`json:"simple_file_list"`
	Num int					`json:"num"`
	counter int
	isDir bool
}

// https://stackoverflow.com/questions/26327391/json-marshalstruct-returns

// FileDesc is data file's descriptor
// uid is used for unique identification number
type FileDesc struct {
	Name string `json:"name"`
	Uid	int 	`json:"uid"`
}


func (ws *workspace) Init(dir string) {
	ws.reset()
	ws.DirName = dir
}

func (ws *workspace) reset() {
	ws.counter = 0
	ws.FileList = make([]FileDesc, 0)
	ws.Num = 0
	ws.isDir = false
}

func (ws *workspace) IsEmpty() bool {
	if len(ws.FileList) == 0 {
		return true
	}
	return false
}

// Get finds corresponding file name with index.
// This only searching through FileList.
func (ws *workspace) Get(index int) (string, bool){
	for _, e := range ws.FileList {
		if e.Uid == index {
			return e.Name, true
		}
	}
	return "", false
}

func (ws *workspace) getFileList(dirName string) {
	files, err := ioutil.ReadDir(dirName)

	if err != nil {
		logger.Logger.Error(err)
		return
	}

	for _, file := range files {
		if file.Name() != ".workspace_info.json" && filepath.Ext(file.Name()) == ".cep" {
			if file.IsDir() {
				ws.isDir = true
				ws.getFileList(dirName + "/" + file.Name())
			} else {
				if ws.isDir {
					logger.Logger.Debug("You have dir called [" + dirName + "]")
					tmp := FileDesc {Name: dirName +"/"+ file.Name(), Uid: ws.counter}
					ws.FileList = append(ws.FileList, tmp)
					ws.counter ++
				} else {
					ws.isDir = false
					tmp := FileDesc {Name:dirName +"/" + file.Name(), Uid: ws.counter}
					ws.counter ++
					ws.FileList = append(ws.FileList, tmp)
				}
			}
		}
	}
}

func (ws *workspace) GetFileList(){
	ws.reset()
	path, err := os.Getwd()
	if err != nil {
		logger.Logger.Error(err)
		return
	}
	logger.Logger.Debug("Get file list from:" + path)  // for example /home/user
	ws.getFileList(ws.DirName)
	ws.Num = ws.counter
}

func (ws *workspace) getFileListWithOutId(dirName string) {
	files, err := ioutil.ReadDir(dirName)

	if err != nil {
		logger.Logger.Error(err)
		return
	}

	for _, file := range files {
		if file.Name() != ".workspace_info.json" && filepath.Ext(file.Name()) == ".cep" {
			if file.IsDir() {
				ws.isDir = true
				ws.getFileListWithOutId(dirName + file.Name())
			} else {
				if ws.isDir {
					logger.Logger.Debug("You have dir called [" + dirName + "]")
					ws.SimpleFileList = append(ws.SimpleFileList, dirName + "/" + file.Name())
				} else {
					ws.isDir = false
					ws.SimpleFileList = append(ws.SimpleFileList,dirName +"/"+ file.Name())
				}
			}
		}
	}
}

func (ws *workspace) GetFileListWithOutId(){
	ws.reset()
	ws.getFileListWithOutId(ws.DirName)
	ws.Num = ws.counter
}