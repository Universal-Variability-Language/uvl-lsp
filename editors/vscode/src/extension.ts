//Credit: Much of this was stolen from zigtools
// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import { workspace, window, ExtensionContext } from 'vscode';
import * as path from "path";
import * as os from "os";
import * as which from "which";
import * as fs from "fs";
import * as mkdirp from "mkdirp";
import * as admzip from "adm-zip";
import * as child_process from "child_process";
import {

	DiagnosticSeverity,
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	Trace,

	TransportKind
} from 'vscode-languageclient/node';
import axios from "axios";
import { manual } from 'mkdirp';
import { posix } from 'path';
import AdmZip = require('adm-zip');
import { start } from 'repl';
import { ClientRequest } from 'http';
import { info } from 'console';

let client: LanguageClient | null = null;
let outputChannel: vscode.OutputChannel | null = null;
const SOURCE_URI = "https://api.github.com/repos/Universal-Variability-Language/uvl-lsp/releases/latest";


function getDefaultInstallationName(): string | null {
	// NOTE: Not using a JS switch because they're ugly as hell and clunky :(

	const plat = process.platform;
	const arch = process.arch;
	if (arch === "x64") {
		if (plat === "linux") return "x86_64-linux";
		else if (plat === "darwin") return "x86_64-macos";
		else if (plat === "win32") return "x86_64-windows";
	} else if (arch === "arm64") {
		if (plat === "darwin") return "aarch64-macos";
		if (plat === "linux") return "aarch64-linux";
	}

	return null;
}
interface Asset {
	name: string,
	browser_download_url: string

}
interface Metadata {
	tag_name: string,
	assets: [Asset],
}
async function fetchInfo(): Promise<Metadata> {
	return (await axios.get<Metadata>(SOURCE_URI)).data
}


async function uvlsPath(context: ExtensionContext) {
	const configuration = workspace.getConfiguration("uvls");
	var uvlsPath = configuration.get<string | null>("path", null);

	if (!uvlsPath) {
		uvlsPath = which.sync('uvls', { nothrow: true });
	} else if (uvlsPath.startsWith("~")) {
		uvlsPath = path.join(os.homedir(), uvlsPath.substring(1));
	} else if (!path.isAbsolute(uvlsPath)) {
		uvlsPath = which.sync(uvlsPath, { nothrow: true });
	}
	const uvlsPathExists = uvlsPath !== null && fs.existsSync(uvlsPath);
	var message: string | null = null;
	if (uvlsPath && uvlsPathExists) {
		try {
			fs.accessSync(uvlsPath, fs.constants.R_OK | fs.constants.X_OK);
		} catch {
			message = `\`uvls.path\` ${uvlsPath} is not an executable`;
		}
		const stat = fs.statSync(uvlsPath);
		if (!stat.isFile()) {
			message = `\`uvls.path\` ${uvlsPath} is not a file`;
		}
	}
	if (message === null) {
		if (!uvlsPath) {
			message = "Couldn't find UVL Language Server (UVLS) executable, please specify it under \`uvls.path\`";
		} else if (!uvlsPathExists) {
			message = `Couldn't find UVL Language Server (UVLS) executable at ${uvlsPath}`;
		}
	}
	if (message) {
		const response = await window.showWarningMessage(message, "Install UVLS", "Specify Path");
		if (response === "Install UVLS") {
			return await installExecutable(context);
		} else if (response === "Specify Path") {
			const uris = await window.showOpenDialog({
				canSelectFiles: true,
				canSelectFolders: false,
				canSelectMany: false,
				title: "Select UVLS executable",
			});

			if (uris) {
				await configuration.update("path", uris[0].path, true);
				return uris[0].path;
			}
		}
		return null;
	}

	return uvlsPath;

}
async function installExecutable(context: ExtensionContext): Promise<string | null> {
	const def = getDefaultInstallationName();
	if (!def) {
		window.showInformationMessage(`Your system isn't built by our CI!\nPlease follow the instructions [here](https://github.com/Caradhrass/uvls) to get started!`);
		return null;
	}
	let archiveName = def.concat(".zip");




	return window.withProgress({
		title: "Installing UVLS...",
		location: vscode.ProgressLocation.Notification,
	}, async progress => {
		progress.report({ message: "Downloading UVLS executable..." });
		let meta = await fetchInfo();
		let tgt = meta.assets.find(e => e.name.endsWith(archiveName));
		if (tgt === undefined) {
			window.showInformationMessage(`Your system isn't built by our CI!\nPlease follow the instructions [here](https://github.com/Caradhrass/uvls) to get started!`);
			return null;
		}
		const url = tgt?.browser_download_url;
		const data = (await axios.get(url!, { responseType: "arraybuffer" })).data;
		const zip = new AdmZip(data);
		const folder = `uvls-${meta.tag_name}-${def}`;
		const name = `uvls${def.endsWith("windows") ? ".exe" : ""}`;

		progress.report({ message: "Installing..." });
		zip.extractEntryTo(`${folder}/${name}`, context.globalStorageUri.fsPath, false, true);
		const installDir = context.globalStorageUri;
		const uvlsBinPath = vscode.Uri.joinPath(installDir, name).fsPath;
		fs.chmodSync(uvlsBinPath, 0o755);

		let config = workspace.getConfiguration("uvls");
		await config.update("path", uvlsBinPath, true);

		return uvlsBinPath;
	});
}
interface Version {
	major: number,
	minor: number,
	patch: number,
}

function parseVersion(str: string): Version | null {
	const matches = /v(\d+)\.(\d+)\.(\d+)/.exec(str);
	//                  0   . 10   .  0  -dev .218   +d0732db
	//                                  (         optional          )?

	if (!matches) return null;
	if (matches.length !== 4 && matches.length !== 7) return null;
	return {
		major: parseInt(matches[1]),
		minor: parseInt(matches[2]),
		patch: parseInt(matches[3]),
	};
}
async function isUpdateAvailable(uvlsPath: string): Promise<boolean | null> {
	let remote = parseVersion(await (await fetchInfo()).tag_name);
	const current = parseVersion(child_process.execFileSync(uvlsPath, ['-v']).toString("utf-8"));
	if (!current || !remote) return null;
	if (remote.major < current.major) return false;
	if (remote.major > current.major) return true;
	if (remote.minor < current.minor) return false;
	if (remote.minor > current.minor) return true;
	if (remote.patch < current.patch) return false;
	if (remote.patch > current.patch) return true;
	return false;
}
async function isUVLSPrebuildBinary(context: ExtensionContext): Promise<boolean> {
	const configuration = workspace.getConfiguration("uvls");
	var uvlsPath = configuration.get<string | null>("path", null);
	if (!uvlsPath) return false;
	const uvlsBinPath = vscode.Uri.joinPath(context.globalStorageUri, "uvls").fsPath;
	return uvlsPath.startsWith(uvlsBinPath);
}

async function checkUpdate(context: ExtensionContext, autoInstallPrebuild: boolean): Promise<void> {
	const configuration = workspace.getConfiguration("uvls");

	const p = await uvlsPath(context);
	if (!p) return;

	if (!await isUpdateAvailable(p)) return;

	const isPrebuild = await isUVLSPrebuildBinary(context);

	if (autoInstallPrebuild && isPrebuild) {
		await installExecutable(context);
	} else {
		const message = `There is a new update available for UVLS. ${!isPrebuild ? "It would replace your installation with a prebuilt binary." : ""}`;
		const response = await window.showInformationMessage(message, "Install update", "Never ask again");

		if (response === "Install update") {
			await installExecutable(context);
		} else if (response === "Never ask again") {
			await configuration.update("auto_update", false, true);
		}
	}
}
async function checkUpdateMaybe(context: ExtensionContext) {
	const configuration = workspace.getConfiguration("uvls");
	const checkForUpdate = configuration.get<boolean>("auto_update", true);
	if (checkForUpdate) await checkUpdate(context, true);
}

export async function activate(context: vscode.ExtensionContext) {

	vscode.commands.registerCommand('uvls.check_for_updates', async () => {
		await stopClient();
		await checkUpdate(context, false);
		await startClient(context);
	});
	vscode.commands.registerCommand('uvls.restart', async () => {
		await stopClient();
		await startClient(context);
	});
	vscode.commands.registerCommand('uvls.open_web', async (args) => {
		const uri = args[0].uri;
		// Create and show a new webview
		const panel = vscode.window.createWebviewPanel(
			'uvlsConfig', // Identifies the type of the webview. Used internally
			'UVLS Configure', // Title of the panel displayed to the user
			vscode.ViewColumn.One, // Editor column to show the new webview panel in.
			{
				enableScripts: true,
				retainContextWhenHidden: true
			} // Webview options. More on these later.
		);
		outputChannel?.appendLine(`${uri}`);
		panel.webview.html = panel.webview.html = `<!DOCTYPE html>
		<html lang="en"">
		<head>
			<meta charset="UTF-8">
			<title>Preview</title>
		</head>
		<body>
			<iframe src="${uri}" style="position:fixed; top:0; left:0; bottom:0; right:0; width:100%; height:100%; border:none; margin:0; padding:0; overflow:hidden; z-index:999999;"></iframe>
		</body>
		</html>`
	})
	await checkUpdateMaybe(context);
	await startClient(context);

}


// This method is called when your extension is deactivated
export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
async function startClient(context: ExtensionContext) {
	const path = await uvlsPath(context);
	if (!path) {
		window.showWarningMessage("Couldn't find Zig Language Server (UVLS) executable");
		return;
	}
	outputChannel = vscode.window.createOutputChannel("UVL Language Server");
	const serverOptions: ServerOptions = {
		command: path, // Replace with your own command.,

	};
	// Decorator for dead features
	const decorators: Array<vscode.TextEditorDecorationType> = new Array(4);
	decorators[0] = vscode.window.createTextEditorDecorationType({
		gutterIconPath: context.asAbsolutePath("assets/deadfeature.svg"),
		gutterIconSize: "90%",
		backgroundColor: { id: 'color.deadfeature' }
	});

	// Decorator for false-optional features
	decorators[1] = vscode.window.createTextEditorDecorationType({
		gutterIconPath: context.asAbsolutePath("assets/falseoptional.svg"),
		gutterIconSize: "90%",
		backgroundColor: { id: 'color.yellow' }
	});

	//Decorator for redundant Constraints
	decorators[2] = vscode.window.createTextEditorDecorationType({
		gutterIconPath: context.asAbsolutePath("assets/redundantconstraint.svg"),
		gutterIconSize: "90%",
		backgroundColor: { id: 'color.yellow' }
	});
	//Decorator for void feature
	decorators[3] = vscode.window.createTextEditorDecorationType({
		gutterIconPath: context.asAbsolutePath("assets/voidfeature.svg"),
		gutterIconSize: "90%",
		backgroundColor: { id: 'color.voidfeature' }
	});
	let rangeOrOptions: Map<String,Array<Array<vscode.Range>>> = new Map();
	
	//If we change the textEditor, the Decoration remains intact 
	window.onDidChangeActiveTextEditor((editor) =>{
		if(editor !== undefined && rangeOrOptions !== null){
			const range = rangeOrOptions.get(editor.document.fileName);
			if(range !== undefined) decorators.forEach((decorator, index) => editor.setDecorations(decorator,range[index]));
		}
	});
	
	let documentSelector = [{ scheme: "file", language: "uvl" }, { scheme: "file", pattern: "**/*.uvl.json" }];
	const clientOptions: LanguageClientOptions = {
		documentSelector,
		outputChannel,
		// middleware implements handleDiagnostic
		middleware: {
			// method are called if server send a notification "textDocument/diagnostic"
			handleDiagnostics(uri, diagnostics, next) {
				// handle anomilies
				const textEditor = window.activeTextEditor;
				if (textEditor !== undefined && textEditor.document.fileName === uri.path) {
					if(!rangeOrOptions.has(textEditor.document.fileName)){
						rangeOrOptions.set(textEditor.document.fileName,[[],[],[],[]]);
					}
					let range = rangeOrOptions.get(textEditor.document.fileName);
					range![0] = [];
					range![1] = [];
					range![2] = [];
					range![3] = [];
					for (const ele of diagnostics) {
						switch (ele.message) {
							case "dead feature": {
								range![0].push(ele.range);
								break;
							}
							case "false-optional feature": {
								range![1].push(ele.range);
								break;
							}
							case "redundant constraint": {
								range![2].push(ele.range);
								break;
							}
							case "void feature model": {
								range![3].push(ele.range);
								break;
							}

						}
					}
					decorators.forEach((decorator, index) => textEditor.setDecorations(decorator, range![index]));
				}
				next(uri, diagnostics);
			},
		}

	};
	outputChannel.appendLine("test");
	client = new LanguageClient('uvls', serverOptions, clientOptions);
	client.onRequest("workspace/executeCommand", async (args) => {
		await vscode.commands.executeCommand(args.command, args.arguments);

	});
	client.setTrace(Trace.Verbose);
	client.start();
}
async function stopClient(): Promise<void> {
	if (client) client.stop();
	client = null;
}