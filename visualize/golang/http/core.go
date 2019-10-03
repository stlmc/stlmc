package http

import (
	"encoding/json"
	"github.com/gorilla/mux"
	"golang/data"
	"log"
	"net/http"
	"os"
	"path/filepath"
	"strconv"
)
// See : https://github.com/gorilla/mux

// spaHandler implements the http.Handler interface, so we can use it
// to respond to HTTP requests. The path to the static directory and
// path to the index file within that static directory are used to
// serve the SPA in the given static directory.
type spaHandler struct {
	staticPath string
	indexPath  string
}

// ServeHTTP inspects the URL path to locate a file within the static dir
// on the SPA handler. If a file is found, it will be served. If not, the
// file located at the index path on the SPA handler will be served. This
// is suitable behavior for serving an SPA (single page application).
func (h *spaHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	// get the absolute path to prevent directory traversal
	path, err := filepath.Abs(r.URL.Path)
	if err != nil {
		// if we failed to get the absolute path respond with a 400 bad request
		// and stop
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	// prepend the path with the path to the static directory
	path = filepath.Join(h.staticPath, path)

	// check whether a file exists at the given path
	_, err = os.Stat(path)
	if os.IsNotExist(err) {
		// file does not exist, serve index.html
		http.ServeFile(w, r, filepath.Join(h.staticPath, h.indexPath))
		return
	} else if err != nil {
		// if we got an error (that wasn't that the file doesn't exist) stating the
		// file, return a 500 internal server error and stop
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	// otherwise, use http.FileServer to serve the static dir
	http.FileServer(http.Dir(h.staticPath)).ServeHTTP(w, r)
}

type StlSever struct {
	spaHandler spaHandler
	router *mux.Router
}

func (ss *StlSever) handleFileList(w http.ResponseWriter, r *http.Request){
	//data.Workspace.GetFileListWithOutId()
	data.Workspace.GetFileList()
	w.WriteHeader(http.StatusCreated)

	// write back to requester
	encodingErr := json.NewEncoder(w).Encode(data.Workspace)

	if encodingErr != nil {
		log.Fatal(encodingErr)
	}
}

func (ss *StlSever) handleSimpleFileList(w http.ResponseWriter, r *http.Request){
	//data.Workspace.GetFileListWithOutId()
	data.Workspace.GetFileListWithOutId()
	w.WriteHeader(http.StatusCreated)

	// write back to requester
	encodingErr := json.NewEncoder(w).Encode(data.Workspace)

	if encodingErr != nil {
		log.Fatal(encodingErr)
	}
}

func (ss *StlSever) handleData(w http.ResponseWriter, r *http.Request){
	if data.Workspace.IsEmpty() {
		data.Workspace.GetFileList()
	}
	vars := mux.Vars(r)
	id, convErr := strconv.Atoi(vars["id"])

	if convErr != nil {
		log.Fatal(convErr)
	}

	res, err := data.Workspace.Get(id)

	if !err {
		log.Fatal("No such file.")
	}


	// searching for database for caching
	val := data.Db.Get(id)

	if val == nil {
		val = data.Json2FullGraph(id, data.Workspace.DirName+res)
	}

	w.WriteHeader(http.StatusCreated)

	// write back to requester
	encodingErr := json.NewEncoder(w).Encode(val.ToFullGraph4Json())

	if encodingErr != nil {
		log.Fatal(encodingErr)
	}
}

func (ss *StlSever) Init() {
	ss.router = mux.NewRouter().StrictSlash(true)
	ss.spaHandler = spaHandler{staticPath:"../build", indexPath:"index.html"}
	ss.router.HandleFunc("/file_list", ss.handleFileList)
	ss.router.HandleFunc("/file/{id:[0-9]+}", ss.handleData)
	ss.router.HandleFunc("/simple_file_list", ss.handleSimpleFileList)
	ss.router.PathPrefix("/").Handler(&ss.spaHandler)
}

func (ss *StlSever) Start() {
	log.Fatal(http.ListenAndServe(":3001", ss.router))
}