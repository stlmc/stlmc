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
		logger.Logger.Error(encodingErr)
		return
	}

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

}


func main() {

	var webDir string
	var port string
	var ip string
	var dir string
	flag.StringVar(&dir, "dir", "./DataDir", "Sets a location (directory) of counter examples. Default location is \"DataDir\" directory.")
	logFlag := flag.Bool("v", false, "Sets verbose option. If this flag is set, a server will show the debug messages.")
	// with out specifying web dir, the server finds ./web directory
	flag.StringVar(&webDir, "web-dir", "./web", "Sets a location (directory) of visualization static web pages. Default location is \"web\" directory.")
	flag.StringVar(&port, "port", "3000", "Sets a server's port number. If you change this you have to rebuild static web pages. This option is for developers.")
	flag.StringVar(&ip, "ip", "0.0.0.0", "Sets a server's ip address. If you change this you have to rebuild static web pages. This option is for developers.")
	flag.Parse()

	logger.Logger.IsDebug = *logFlag

	// https://medium.com/@int128/shutdown-http-server-by-endpoint-in-go-2a0e2d7f9b8c
	// https://jaehue.github.io/post/how-to-use-golang-context/
	// http://golang.site/go/article/22-Go-%EC%B1%84%EB%84%90

	var ss http2.StlSever
	//var wait time.Duration
	data.Workspace.Init(dir)

	//ctx, cancel := context.WithTimeout(context.Background(), wait)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()


	ss.Init(cancel, webDir, ip, port)
	go ss.Start()
	select{
	case <-ctx.Done():
		ss.Shutdown(ctx)
	}
}