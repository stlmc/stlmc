const electron = require('electron');
const app = electron.app;
const BrowserWindow = electron.BrowserWindow;

const path = require('path');
const isDev = require('electron-is-dev');

let mainWindow;


const {
    Menu,
    MenuItem,
    ipcMain,
} = require('electron');

const menu = new Menu();
menu.append(new MenuItem({ label: 'Hello' }));
menu.append(new MenuItem({ type: 'separator' }));
menu.append(new MenuItem({ label: 'Electron', type: 'checkbox', checked: true }));

app.on('browser-window-created', (event, win) => {
    win.webContents.on('context-menu', (e, params) => {
        menu.popup(win, params.x, params.y);
    })
});

ipcMain.on('show-context-menu', (event) => {
    const win = BrowserWindow.fromWebContents(event.sender);
    menu.popup(win)
});

function createWindow() {
    mainWindow = new BrowserWindow({width: 1600, height: 900,
        //The lines below solved the issue
        //https://stackoverflow.com/questions/19059580/client-on-node-uncaught-referenceerror-require-is-not-defined
        webPreferences: {
            nodeIntegration: true
        }
    });
    // original : isDev ? 'http://localhost:3000' : `file://${path.join(__dirname, '../build/index.html')}`
    mainWindow.loadURL(`file://${path.join(__dirname, '../build/index.html')}`);
    if (isDev) {
        // Open the DevTools.
        //BrowserWindow.addDevToolsExtension('<location to your react chrome extension>');
        mainWindow.webContents.openDevTools();
    }
    mainWindow.on('closed', () => mainWindow = null);
}

app.on('ready', createWindow);
/*
app.on('browser-window-created', (event, win) => {
   win.webContents.on('context-menu', (e, params) => {
       menu.popup(win, params.x, params.y);
   })
});


ipcMain.on('show-context-menu', (event) => {
    const win = BrowserWindow.fromWebContents(event.sender);
    menu.popup(win);
});*/

app.on('window-all-closed', () => {
    if (process.platform !== 'darwin') {
        app.quit();
    }
});

app.on('activate', () => {
    if (mainWindow === null) {
        createWindow();
    }
});