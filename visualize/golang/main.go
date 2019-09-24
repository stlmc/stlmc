package main

import (
	"encoding/json"
	"fmt"
	"github.com/gorilla/mux"
	"io/ioutil"
	"log"
	"net/http"
	"strings"
)

const DirName = "../src/DataDir/"

type event struct {
	ID [] string `json:"file_list"`
}

//https://medium.com/the-andela-way/build-a-restful-json-api-with-golang-85a83420c9da

func homeLink(w http.ResponseWriter, r *http.Request) {
	fmt.Fprintf(w, "Welcome home!")
}

// TODO: change result [] string to pointer
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

func main() {
	router := mux.NewRouter().StrictSlash(true)
	router.HandleFunc("/", homeLink)
	router.HandleFunc("/update", updateWorkspace)
	log.Fatal(http.ListenAndServe(":3001", router))
}