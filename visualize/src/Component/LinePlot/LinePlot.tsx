import React from 'react';
import lineplotStyle from './style/LinePlot.module.scss';
import styleVariable from './style/variable.module.scss';
import './style/LinePlotStyle.scss';
import {margin, size} from '../Core/Util/Util';
import {Renderer} from '../Core/Renderer/MainRenderer';
import {PropositionRenderer} from '../Core/Renderer/PropositionRenderer';
import {Json, WorkspaceJson} from '../Core/Util/DataParser';
import Select from 'react-select';
import {ActionMeta, ValueType} from 'react-select/src/types';
import {Tab, Tabs, TabList, TabPanel} from 'react-tabs';
import "react-tabs/style/react-tabs.css";


//import {ipcRenderer} from 'electron';
// Tell main process to show the menu when demo button is clicked
/*
const contextMenuBtn = document.getElementById('context-menu');

contextMenuBtn!.addEventListener('click', () => {
    ipcRenderer.send('show-context-menu');
});*/
/*
 * Props and State
 */
interface Props {
}

interface Popup {
    isEnabled: boolean;
}

interface State {
    popup: Popup;
    selectedVariables: string[];
    allVariables: string[];
    isRedraw: boolean;

    selectedProps: string[];
    allProps: string[];
}

/*
 * LinePlot Component
 * no longer need constructors
 * https://medium.com/@martin_hotell/react-typescript-and-defaultprops-dilemma-ca7f81c661c7
 */
class LinePlot extends React.Component<Props, State> {

    private width: number = parseFloat(styleVariable.width.replace("px", ""));
    private height: number = parseFloat(styleVariable.height.replace("px", ""));
    private width_viewer: number = parseFloat(styleVariable.width_viewer.replace("px", ""));
    private height_viewer: number = parseFloat(styleVariable.height_viewer.replace("px", ""));
    private width_controller: number = parseFloat(styleVariable.width_controller.replace("px", ""));
    private height_controller: number = parseFloat(styleVariable.height_controller.replace("px", ""));

    private margin_viewer_top: number = parseFloat(styleVariable.margin_viewer_top.replace("px", ""));
    private margin_viewer_right: number = parseFloat(styleVariable.margin_viewer_right.replace("px", ""));
    private margin_viewer_bottom: number = parseFloat(styleVariable.margin_viewer_bottom.replace("px", ""));
    private margin_viewer_left: number = parseFloat(styleVariable.margin_viewer_left.replace("px", ""));

    private margin_controller_top: number = parseFloat(styleVariable.margin_controller_top.replace("px", ""));
    private margin_controller_right: number = parseFloat(styleVariable.margin_controller_right.replace("px", ""));
    private margin_controller_bottom: number = parseFloat(styleVariable.margin_controller_bottom.replace("px", ""));
    private margin_controller_left: number = parseFloat(styleVariable.margin_controller_left.replace("px", ""));

    private renderer: Renderer = new Renderer(
        new size(
            this.width,
            this.height,
            this.width_viewer,
            this.height_viewer,
            this.width_controller,
            this.height_controller
        ),
        new margin(
            this.margin_viewer_top,
            this.margin_viewer_right,
            this.margin_viewer_bottom,
            this.margin_viewer_left
        ),
        new margin(
            this.margin_controller_top,
            this.margin_controller_right,
            this.margin_controller_bottom,
            this.margin_controller_left
        ),
        // need to concat . before string of className for d3.js
        // https://www.tutorialspoint.com/d3js/d3js_selections.htm
        "#graph"
    );

    private propRenderers: PropositionRenderer[] = [];

    private propRenderer: PropositionRenderer = new PropositionRenderer(
        new size(
            this.width,
            this.height,
            this.width_viewer,
            this.height_viewer,
            this.width_controller,
            this.height_controller
        ),
        new margin(
            this.margin_viewer_top,
            this.margin_viewer_right,
            this.margin_viewer_bottom,
            this.margin_viewer_left
        ),
        new margin(
            this.margin_controller_top,
            this.margin_controller_right,
            this.margin_controller_bottom,
            this.margin_controller_left
        ),
        // need to concat . before string of className for d3.js
        // https://www.tutorialspoint.com/d3js/d3js_selections.htm
        "#graph"
    );

    private propRenderer2: PropositionRenderer = new PropositionRenderer(
        new size(
            this.width,
            this.height,
            this.width_viewer,
            this.height_viewer,
            this.width_controller,
            this.height_controller
        ),
        new margin(
            this.margin_viewer_top,
            this.margin_viewer_right,
            this.margin_viewer_bottom,
            this.margin_viewer_left
        ),
        new margin(
            this.margin_controller_top,
            this.margin_controller_right,
            this.margin_controller_bottom,
            this.margin_controller_left
        ),
        // need to concat . before string of className for d3.js
        // https://www.tutorialspoint.com/d3js/d3js_selections.htm
        "#graph",
        1
    );


    private json = new Json("");
    private workspace_info = new WorkspaceJson(require('../../DataDir/.workspace_info.json'));

    // this will get error if change './data/test.json' to this.props.jsonpath
    state: State = {
        popup: {
            isEnabled: true,
        },
        selectedVariables: [],
        allVariables: [],
        isRedraw: false,

        selectedProps: [],
        allProps: [],
    };

    constructor(props: Props) {
        super(props);
        this.onPopupChange = this.onPopupChange.bind(this);
        this.onPopupClick = this.onPopupClick.bind(this);
        this.onPropSelect = this.onPropSelect.bind(this);
        this.onPropListSelect = this.onPropListSelect.bind(this);
        this.onVariablesChange = this.onVariablesChange.bind(this);
    }

    componentDidMount() {
        // must invoke setdata() before draw()
        this.renderer.setdata(this.json);
        //this.propRenderer.setdata(this.json);
        //this.propRenderer2.setdata(this.json);
        this.setState({
            selectedVariables: this.json.variables,
            allVariables: this.json.variables,
            isRedraw: false,

            selectedProps: this.json.propNames,
            allProps: this.json.propNames,
        })
    }

    componentDidUpdate(prevProps: Readonly<Props>, prevState: Readonly<State>, snapshot?: any): void {
        console.log("ComponentUpdate");
        console.log(this.state.selectedVariables);
        this.renderer.selectedVariables = this.state.selectedVariables;

        console.log(this.state.isRedraw);
        // redraw whole thing.
        this.renderer.reload(this.json.isEmpty(), this.json.propNames[0], this.state.isRedraw);
        this.renderer.resize(this.json.propNames.length);
        //this.propRenderer.reload(this.json.isEmpty(), this.json.propNames[0], this.state.isRedraw);
        //this.propRenderer2.reload(this.json.isEmpty(), this.json.propNames[1], this.state.isRedraw);
        for (let e = 0; e < this.state.selectedProps.length; e++) {
            this.propRenderers[e].reload(this.json.isEmpty(), this.state.selectedProps[e], this.state.isRedraw);
        }
    }

    onPopupChange(e: React.ChangeEvent<HTMLInputElement>) {
    }

    onPopupClick(e: React.MouseEvent<HTMLInputElement, MouseEvent>) {
        this.setState({
            popup: {
                isEnabled: e.currentTarget.checked
            }
        }, () => {
            this.renderer.updatePopup(this.state.popup.isEnabled)
        });
        console.log("mouse event");
        console.log(this.state)
    }

    onPropSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {
        //this.renderer.redrawPropCanvas((value2 as { value: string, label: string; })["value"]);
        console.log(`action: ${actionMeta.action}`);
        let target = (value2 as ({ value: string; label: string; }[]));

        let tmp: string[] = [];
        if (target) {
            for (let el of target) {
                tmp.push(el["value"])
            }
        }
        if (actionMeta.action == "remove-value") {
            this.setState({
                selectedProps: tmp,
            });
        } else if (actionMeta.action == "select-option") {
            this.setState({
                selectedProps: tmp,
            });
        } else if (actionMeta.action == "clear") {
            this.setState({
                selectedProps: [],
            });
        }
    }

    onPropListSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {

        this.json.string = require("../../DataDir/" + (value2 as { value: string; label: string; })["value"]);
        this.renderer.setdata(this.json);
        this.propRenderers = [];
        for (let e = 0; e < this.json.propNames.length; e++) {
            let pr = new PropositionRenderer(
                new size(
                    this.width,
                    this.height,
                    this.width_viewer,
                    this.height_viewer,
                    this.width_controller,
                    this.height_controller
                ),
                new margin(
                    this.margin_viewer_top,
                    this.margin_viewer_right,
                    this.margin_viewer_bottom,
                    this.margin_viewer_left
                ),
                new margin(
                    this.margin_controller_top,
                    this.margin_controller_right,
                    this.margin_controller_bottom,
                    this.margin_controller_left
                ),
                // need to concat . before string of className for d3.js
                // https://www.tutorialspoint.com/d3js/d3js_selections.htm
                "#graph",
                e
            );
            pr.setdata(this.json);
            this.propRenderers.push(pr);
        }

        //this.propRenderer.setdata(this.json);
        //this.propRenderer2.setdata(this.json);
        // get reloaded new variables.
        this.setState({
            allVariables: this.json.variables,
            selectedVariables: this.json.variables,
            isRedraw: false,

            allProps: this.json.propNames,
            selectedProps: this.json.propNames,
        });
    }

    // This will get multiple choices.
    onVariablesChange(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {
        console.log(`action: ${actionMeta.action}`);
        let target = (value2 as ({ value: string; label: string; }[]));

        let tmp: string[] = [];
        if (target) {
            for (let el of target) {
                tmp.push(el["value"])
            }
        }
        if (actionMeta.action == "remove-value") {
            this.setState({
                selectedVariables: tmp,
                isRedraw: true,
            });
        } else if (actionMeta.action == "select-option") {
            this.setState({
                selectedVariables: tmp,
                isRedraw: true,
            });
        } else if (actionMeta.action == "clear") {
            this.setState({
                selectedVariables: [],
                isRedraw: true,
            });
        }
    }

    render() {
        let options = this.state.allVariables.map((v) => {
            return ({value: v, label: v})
        });
        let selected = this.state.selectedVariables.map((v) => {
            return ({value: v, label: v})
        });
        let props = [{value: "All", label: "All"}].concat(this.state.allProps.map(
            (v) => {
                //this.json.proposition_names[v]
                return ({
                    value: v,
                    label: (v + " = (" + this.json.proposition_names[v] + ")")
                });
            }));
        let selectedProps = this.state.selectedProps.map((v) => {
            return ({value: v, label: v})
        });
        // TODO: Update precision of graph after update.
        return (
            <div>
                <div className="row">
                    <div className="col-md-1"/>
                    <div className="col-md-10">
                        <label>Models</label>
                        <Select isSearchable={true} options={this.workspace_info.file_list.map(
                            (v) => {
                                return ({value: v, label: v});
                            }
                        )} onChange={this.onPropListSelect}/>
                    </div>
                    <div className="col-md-1"/>
                </div>

                {!this.json.isEmpty() ?
                    (
                        <div>
                            <div className="row basic_box">
                                <div className="col-md-12">
                                    <Tabs>
                                        <TabList>
                                            <Tab>Title 1</Tab>
                                            <Tab>Title 2</Tab>
                                        </TabList>

                                        <TabPanel forceRender={true}>

                                            <div className="row">
                                                <div className="col-md-1"/>
                                                <div className="col-md-10">
                                                    <label>Variables</label>
                                                    <Select className="select_theme" options={options}
                                                            onChange={this.onVariablesChange}
                                                            value={selected}
                                                            isMulti={true} isSearchable={true}
                                                            closeMenuOnSelect={false}>
                                                    </Select>
                                                </div>
                                                <div className="col-md-1"/>
                                            </div>

                                            <div className="row line_plot_container">
                                                <div className="col-md-1"/>
                                                <div className="col-md-10">
                                                    <label>Propositions</label>
                                                    <Select isSearchable={true} options={props}
                                                            onChange={this.onPropSelect}
                                                            value={selectedProps}
                                                            isMulti={true}
                                                            closeMenuOnSelect={false}/>
                                                </div>
                                                <div className="col-md-1"/>
                                            </div>

                                            <div className="row basic_box">
                                                <div className="col-md-1"/>
                                                <div className="col-md-7"/>
                                                <div className="col-md-4">
                                                    <div className="form-check text-right">
                                                        <label>Enabled Popups &nbsp;
                                                            <input className="form-check-input" type="checkbox"
                                                                   checked={this.state.popup.isEnabled} onClick={this.onPopupClick}
                                                                   onChange={this.onPopupChange}/>
                                                        </label>
                                                    </div>
                                                </div>
                                            </div>

                                            <div className="row">
                                                <div className="svg_div" id="graph"/>
                                            </div>



                                        </TabPanel>
                                        <TabPanel>
                                            <h2>Any content 2</h2>
                                        </TabPanel>
                                    </Tabs>


                                </div>
                            </div>


                        </div>
                    )
                    : (
                        <div className="row line_plot_div">
                            <div className="col-md-1"/>
                            <div className="col-md-10 alert alert-warning" role="alert">
                                Nothing to show!
                            </div>
                            <div className="col-md-1"/>
                        </div>
                    )}
            </div>);
    }
}

export default LinePlot;