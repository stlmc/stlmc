package main

// TODO: DirName not exist exception...
import (
	"encoding/json"
	"fmt"
	"github.com/gorilla/mux"
	"golang/util"
	"io/ioutil"
	"log"
	"net/http"
	"strings"
)

const DirName = "../../src/DataDir/"

// https://stackoverflow.com/questions/26327391/json-marshalstruct-returns

type event struct {
	ID [] string `json:"file_list"`
}

// fileDesc is data file's descriptor
// uid is used for unique identification number
type fileDesc struct {
	Name string `json:"name"`
	Uid	uint64 	`json:"uid"`
}

type fileList struct {
	List [] fileDesc `json:"file_list"`
	Num uint64 		`json:"num"`
}

//https://medium.com/the-andela-way/build-a-restful-json-api-with-golang-85a83420c9da

func homeLink(w http.ResponseWriter, r *http.Request) {
	fmt.Fprintf(w, "Welcome home!")
}

func ureadDir(dirName string, result *[]fileDesc, isDir bool, counter *uint64) {
	files, err := ioutil.ReadDir(dirName)

	if err != nil {
		log.Fatal(err)
	}

	for _, file := range files {
		if file.Name() != ".workspace_info.json" {
			if file.IsDir() {
				ureadDir(dirName + file.Name(), result, true, counter)
			} else {
				if isDir {
					dirName = strings.Trim(dirName, DirName)
					fmt.Println("You have dir called [" + dirName + "]")
					tmp := fileDesc {Name:dirName + "/" + file.Name(), Uid: *counter}
					*result = append(*result, tmp)
					*counter ++
				} else {
					tmp := fileDesc {Name:file.Name(), Uid: *counter}
					*counter ++
					*result = append(*result, tmp)
				}
			}
		}
	}
}

func readDir(dirName string, result *[]string, isDir bool) {
	files, err := ioutil.ReadDir(dirName)

	if err != nil {
		log.Fatal(err)
	}

	for _, file := range files {
		if file.Name() != ".workspace_info.json" {
			if file.IsDir() {
				readDir(dirName + file.Name(), result, true)
			} else {
				if isDir {
					dirName = strings.Trim(dirName, DirName)
					fmt.Println("You have dir called [" + dirName + "]")
					*result = append(*result, dirName + "/" + file.Name())
				} else {
					*result = append(*result, file.Name())
				}
			}
		}
	}
}

func updateWorkspace(w http.ResponseWriter, r *http.Request){

	var newEvent event
	var result []string
	readDir(DirName, &result, false)
	newEvent.ID = result

	w.WriteHeader(http.StatusCreated)
	encodingErr := json.NewEncoder(w).Encode(newEvent)

	if encodingErr != nil {
		log.Fatal(encodingErr)
	}

	file, marshalErr := json.Marshal(newEvent)

	if marshalErr != nil {
		log.Fatal(marshalErr)
	}

	writeError := ioutil.WriteFile(DirName + ".workspace_info.json", file, 0644)

	if writeError != nil {
		log.Fatal(writeError)
	}
}

func test(w http.ResponseWriter, r *http.Request){

	var newEvent fileList
	var result []fileDesc
	var counter uint64
	counter = 0
	ureadDir(DirName, &result, false, &counter)

	newEvent.List = result
	newEvent.Num = counter

	w.WriteHeader(http.StatusCreated)

	// write back to requester
	encodingErr := json.NewEncoder(w).Encode(newEvent)

	if encodingErr != nil {
		log.Fatal(encodingErr)
	}

	file, marshalErr := json.Marshal(newEvent)

	if marshalErr != nil {
		log.Fatal(marshalErr)
	}

	writeError := ioutil.WriteFile(DirName + ".workspace_info.json", file, 0644)

	if writeError != nil {
		log.Fatal(writeError)
	}
}


func main() {
	util.Read(DirName+"oneThermostatMix_([]_[0.0,40.0]^[0.0,inf) (~ reachability))_3.json")
	router := mux.NewRouter().StrictSlash(true)
	router.HandleFunc("/", homeLink)
	router.HandleFunc("/update", updateWorkspace)
	router.HandleFunc("/test", test)
	log.Fatal(http.ListenAndServe(":3001", router))
}