package main

// TODO: DirName not exist exception...
import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"golang/data"
	http2 "golang/http"
	"golang/logger"
	"log"
	"net/http"
)

type event struct {
	ID [] string `json:"file_list"`
}


//https://medium.com/the-andela-way/build-a-restful-json-api-with-golang-85a83420c9da

func homeLink(w http.ResponseWriter, r *http.Request) {
	fmt.Fprintf(w, "Welcome home!")
}


func updateWorkspace(w http.ResponseWriter, r *http.Request){

	data.Workspace.GetFileListWithOutId()
	var newEvent event
	newEvent.ID = data.Workspace.SimpleFileList


	w.WriteHeader(http.StatusCreated)
	encodingErr := json.NewEncoder(w).Encode(newEvent)

	if encodingErr != nil {
		log.Fatal(encodingErr)
	}
/*
	file, marshalErr := json.Marshal(newEvent)

	if marshalErr != nil {
		log.Fatal(marshalErr)
	}

	writeError := ioutil.WriteFile(data.DirName + ".workspace_info.json", file, 0644)

	if writeError != nil {
		log.Fatal(writeError)
	}*/
}

func test(w http.ResponseWriter, r *http.Request){


	//data.Workspace.GetFileListWithOutId()
	data.Workspace.GetFileList()
	var newEvent event
	newEvent.ID = data.Workspace.SimpleFileList

	w.WriteHeader(http.StatusCreated)

	// write back to requester
	encodingErr := json.NewEncoder(w).Encode(data.Workspace)

	if encodingErr != nil {
		log.Fatal(encodingErr)
	}
/*
	file, marshalErr := json.Marshal(event)

	if marshalErr != nil {
		log.Fatal(marshalErr)
	}

	writeError := ioutil.WriteFile(data.Workspace.DirName + ".workspace_info.json", file, 0644)

	if writeError != nil {
		log.Fatal(writeError)
	}*/
}


func main() {

	var dir string
	logFlag := flag.Bool("v", false, "a string?")
	flag.StringVar(&dir, "dir", ".", "the directory to serve files from. Defaults to the current dir")
	flag.Parse()

	logger.Logger.IsDebug = *logFlag
	//data.Json2FullGraph(data.Workspace.DirName+"singleMode_(<>_[0.0,40.0]^[0.0,inf) (xl2 and ([]_[3.0,10.0]^[0.0,inf) (~ xl1))))_3.json")
	//data.SendFullGraph2Json()

	// https://medium.com/@int128/shutdown-http-server-by-endpoint-in-go-2a0e2d7f9b8c
	// https://jaehue.github.io/post/how-to-use-golang-context/
	// http://golang.site/go/article/22-Go-%EC%B1%84%EB%84%90

	var ss http2.StlSever
	//var wait time.Duration

	//ctx, cancel := context.WithTimeout(context.Background(), wait)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()


	ss.Init(cancel)
	go ss.Start()
	select{
	case <-ctx.Done():
		ss.Shutdown(ctx)
	}
}