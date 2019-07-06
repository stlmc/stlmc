import React from 'react';
import lineplotStyle from './style/LinePlot.module.scss';
import styleVariable from './style/variable.module.scss';
import {margin, size} from '../Core/Util/Util';
import {Renderer} from '../Core/Renderer/MainRenderer';
import {Json, WorkspaceJson} from '../Core/Util/DataParser';
import Select from 'react-select';
import {ActionMeta, ValueType} from 'react-select/src/types';

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
        "." + lineplotStyle.main_theme
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
        console.log(this.json.isEmpty());
        this.renderer.setdata(this.json);
        this.setState({
            selectedVariables: this.json.variables,
            allVariables: this.json.variables,
            isRedraw: false,
        })
    }

    componentDidUpdate(prevProps: Readonly<Props>, prevState: Readonly<State>, snapshot?: any): void {
        console.log("ComponentUpdate");
        console.log(this.state.selectedVariables);
        this.renderer.selectedVariables = this.state.selectedVariables;

        console.log(this.state.isRedraw);
        // redraw whole thing.
        this.renderer.reload(this.json.isEmpty(), this.json.propNames[0], this.state.isRedraw);
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
        this.renderer.redrawPropCanvas((value2 as { value: string, label: string; })["value"]);
    }

    onPropListSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {

        this.json.string = require("../../DataDir/" + (value2 as { value: string; label: string; })["value"]);
        this.renderer.setdata(this.json);
        // get reloaded new variables.
        this.setState({
            allVariables: this.json.variables,
            selectedVariables: this.json.variables,
            isRedraw: false,
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
        // TODO: Update precision of graph after update.
        return (
            <div id="graph" className={lineplotStyle.main_theme}>
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
                <div className="row">
                    <div className="col-md-1"/>
                    <div className="col-md-10">
                        <label>Propositions</label>
                        <Select isSearchable={true} options={this.json.propNames.map(
                            (v) => {
                                //this.json.proposition_names[v]
                                return ({
                                    value: v,
                                    label: (v + " = (" + this.json.proposition_names[v] + ")")
                                });
                            }
                        )} onChange={this.onPropSelect}/>
                    </div>
                    <div className="col-md-1"/>
                </div>
                {!this.json.isEmpty() ?
                    (<div>
                            <div className="row">
                                <div className="col-md-1"/>
                                <div className="col-md-4">
                                    <div className="form-check">
                                        <label>Enabled Popups &nbsp;
                                            <input className="form-check-input" type="checkbox"
                                                   checked={this.state.popup.isEnabled} onClick={this.onPopupClick}
                                                   onChange={this.onPopupChange}/>
                                        </label>
                                    </div>
                                </div>
                                <div className="col-md-7"/>
                            </div>

                        </div>
                    )
                    : (
                        <div className="alert alert-warning" role="alert">
                            Nothing to show!
                        </div>
                    )}
            </div>);
    }
}

export default LinePlot;