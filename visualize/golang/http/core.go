package http

import (
	"context"
	"encoding/json"
	"github.com/gorilla/handlers"
	"github.com/gorilla/mux"
	"golang/data"
	"golang/logger"
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
	server *http.Server
	cancel context.CancelFunc
}

func (ss *StlSever) handleFileList(w http.ResponseWriter, r *http.Request){
	//data.Workspace.GetFileListWithOutId()
	logger.Logger.Debug("Data request for file list")
	data.Workspace.GetFileList()
	w.WriteHeader(http.StatusCreated)

	// write back to requester
	encodingErr := json.NewEncoder(w).Encode(data.Workspace)

	if encodingErr != nil {
		logger.Logger.Error(encodingErr)
	}
}

func (ss *StlSever) handleSimpleFileList(w http.ResponseWriter, r *http.Request){
	data.Workspace.GetFileListWithOutId()
	w.WriteHeader(http.StatusCreated)

	// write back to requester
	encodingErr := json.NewEncoder(w).Encode(data.Workspace)

	if encodingErr != nil {
		logger.Logger.Error(encodingErr)
	}
}

func (ss *StlSever) handleData(w http.ResponseWriter, r *http.Request){
	// update workspace
	data.Workspace.GetFileList()

	// update database
	vars := mux.Vars(r)
	logger.Logger.Debug("Data request for file number ", vars["id"])
	id, convErr := strconv.Atoi(vars["id"])

	if convErr != nil {
		logger.Logger.Error(convErr)
		return
	}

	res, err := data.Workspace.Get(id)

	if !err {
		logger.Logger.Error("No such file.")
		return
	}


	// searching for database for caching
	val := data.Json2FullGraph(id, res)

	w.WriteHeader(http.StatusCreated)

	if val != nil {
		// write back to requester
		encodingErr := json.NewEncoder(w).Encode(val.ToCompositeGraph4Json())

		if encodingErr != nil {
			logger.Logger.Error(encodingErr)
			return
		}
	}
}

func (ss *StlSever) handleShutdown(w http.ResponseWriter, r *http.Request) {
	_, _ = w.Write([]byte("Shutdown called"))
	ss.cancel()
}

func (ss *StlSever) Init(cancel context.CancelFunc, webDir string, ip string, port string) {
	ss.router = mux.NewRouter().StrictSlash(true)
	ss.spaHandler = spaHandler{staticPath:webDir, indexPath:"index.html"}
	ss.router.HandleFunc("/file_list", ss.handleFileList)
	ss.router.HandleFunc("/file/{id:[0-9]+}", ss.handleData)
	ss.router.HandleFunc("/simple_file_list", ss.handleSimpleFileList)
	ss.router.HandleFunc("/shutdown", ss.handleShutdown)
	ss.router.PathPrefix("/").Handler(&ss.spaHandler)
	ss.server = &http.Server{
		Addr:              ip+":"+port,
		Handler:           handlers.CORS()(ss.router),
	}
	ss.cancel = cancel
}

func (ss *StlSever) Start() {
	logger.Logger.Print("Welcome to visualize server!")
	logger.Logger.Print("server starts at " + ss.server.Addr)
	if err := ss.server.ListenAndServe(); err != nil {
		logger.Logger.Debug("error occured...")
		log.Fatal(err)
	}
}

func (ss *StlSever) Shutdown(ctx context.Context){
	_ = ss.server.Shutdown(ctx)
	logger.Logger.Print("Shutting down server...")
}