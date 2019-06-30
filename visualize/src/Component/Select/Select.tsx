import React from 'react';
import Select from 'react-select';
import { ValueType, ActionMeta } from 'react-select/src/types';

interface Props{

}

interface State {
    variables: { value: string; label: string;}[];
}

class SelectComponent extends React.Component<Props, State> {
  state:State = {
      variables: [],
  }

  constructor(props:Props){
    super(props)
    this.handleChange = this.handleChange.bind(this)
  }

  handleChange (variables:{ value: string; label: string;}[]) {
    this.setState({ variables: variables });
    console.log(`Option selected:`, variables);
  }

  render() {
    const { variables } = this.state;

    return (
      <Select
        { ... variables}
        //value={variables}
        isClearable={true}
        isSearchable={true}
        isMulti={true}
        options={variables}
      />
    );
  }
}

export default SelectComponent