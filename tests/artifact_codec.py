"""Versioned artifact round trips and hostile-input rejection contracts."""
import gzip
import json
from pathlib import Path
import pickle
import sys
import tempfile
import unittest
from unittest import mock

PROJECT_ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(PROJECT_ROOT/'src'))

from stlmc.artifacts import codec
from stlmc.constraints import constraints as c
from stlmc.solver.dreal import DrealInterval


def example(goal=None):
    x=c.Real('x')
    mode=c.Bool('enabled')
    predicate=c.Geq(x,c.RealVal('1/3'))
    modules=[dict(mode=c.And([mode]),inv=c.And([predicate]),
                  flow=c.Ode([x],[c.Neg(x)]),jump={predicate:c.And([mode])},jp_d={}),
             dict(mode=c.Not(mode),inv=c.BoolVal('True'),
                  flow=c.Function([x],[c.Add(x,c.Real('time'))]),jump={},jp_d={})]
    return ({c.Real('x_0_0'):DrealInterval('0.3333333333333333','0.3333333333333334'),
             c.Real('tau_0'):c.RealVal('1e-20'),c.Int('counter'):c.IntVal('-12345678901234567890'),
             mode:c.BoolVal('False')}, modules, {'enabled':mode}, {mode:predicate},
            {x:(True,c.RealVal('-10'),c.RealVal('10'),False)}, {mode:predicate},
            predicate if goal is None else goal, 'f1', .01, c.And([predicate]),
            {c.Real('constant'):c.RealVal('12345678901234567890/7')})


class ArtifactCodecTest(unittest.TestCase):
    def roundtrip(self,data):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'example.counterexample'
            codec.dump_artifact(path,data,metadata={'producer':'test'})
            self.assertEqual(path.read_bytes()[:2],b'\x1f\x8b')
            document=json.loads(gzip.decompress(path.read_bytes()))
            self.assertIsInstance(document,dict)
            self.assertEqual(document['format'],'stlmc-artifact')
            self.assertEqual(document['schema_version'],1)
            restored=codec.load_artifact(path)
        self.assertIsInstance(restored,tuple)
        self.assertEqual(len(restored),11)
        return restored

    def test_eleven_fields_preserve_types_exact_numbers_and_dreal_boxes(self):
        data=example()
        restored=self.roundtrip(data)
        self.assertEqual(restored[7:9],data[7:9])
        for variable,value in data[0].items():
            actual=restored[0][variable]
            self.assertIs(type(actual),type(value))
            self.assertEqual(actual.value,value.value)
            if isinstance(value,DrealInterval):
                self.assertEqual((actual.lower,actual.upper),(value.lower,value.upper))
        self.assertIsInstance(restored[1][0]['flow'],c.Ode)
        self.assertIsInstance(restored[1][1]['flow'],c.Function)
        for index in (1,2,3,4,5,6,9,10):
            self.assertEqual(str(restored[index]),str(data[index]))

    def test_same_data_metadata_produce_same_bytes_without_temporary_filename(self):
        with tempfile.TemporaryDirectory() as directory:
            first=Path(directory)/'one.counterexample'
            second=Path(directory)/'different.witness'
            data=example()
            with mock.patch.object(codec,'package_version',return_value='test'), \
                    mock.patch.object(codec,'source_commit',return_value='0123456789ab'):
                codec.dump_artifact(first,data,metadata={'purpose':'determinism'})
                codec.dump_artifact(second,data,metadata={'purpose':'determinism'})
            self.assertEqual(first.read_bytes(),second.read_bytes())
            self.assertEqual(first.read_bytes()[3]&8,0,'gzip FNAME must be absent')

    def test_narrow_dreal_representative_preserved_without_certificate_claim(self):
        endpoint='0.1000000000000000000000001'
        interval=DrealInterval(endpoint,endpoint)
        self.assertEqual(interval.value,'0.1')
        data=list(example())
        data[0]={c.Real('x'):interval}
        result=self.roundtrip(tuple(data))[0][c.Real('x')]
        self.assertEqual((result.lower,result.upper,result.value),(endpoint,endpoint,'0.1'))
        data[0]={c.Real('x'):DrealInterval('2','1')}
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError,'interval bounds'):
                codec.dump_artifact(Path(directory)/'bad.counterexample',tuple(data))

    def test_oversized_raw_json_numbers_are_rejected(self):
        numbers=['9'*5000,'0.'+'1'*5000,'1e10001','1e1000','1e999999']
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'bad.counterexample'
            for number in numbers:
                path.write_bytes(gzip.compress(('{"value":'+number+'}').encode()))
                with self.subTest(number=number[:20]),self.assertRaisesRegex(ValueError,'limit|non-finite|exponent'):
                    codec.load_artifact(path)

    def test_truncated_legacy_symbol_is_explicitly_rejected_on_write_and_read(self):
        name='parEndfall^{6,6}_'+'a'*60+'...'
        data=list(example())
        data[0]={c.Bool(name):c.BoolVal('True')}
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'bad.counterexample'
            with self.assertRaisesRegex(ValueError,'truncated symbol identifier.*regenerate'):
                codec.dump_artifact(path,tuple(data))
            codec.dump_artifact(path,example())
            document=json.loads(gzip.decompress(path.read_bytes()))
            document['data']['items'][0]={'tag':'dict','items':[
                [{'tag':'Bool','id':name},{'tag':'BoolVal','value':'True'}]]}
            path.write_bytes(gzip.compress(json.dumps(document).encode()))
            with self.assertRaisesRegex(ValueError,'truncated symbol identifier.*regenerate'):
                codec.load_artifact(path)

    def test_yices_assignment_uses_exact_names_not_pretty_printer(self):
        try:
            from stlmc.solver import yices as backend
        except (ImportError,OSError) as error:
            self.skipTest('optional Yices binding/native library unavailable: '+str(error))
        names={1:'real_'+'r'*120,2:'int_'+'i'*120,3:'bool_'+'b'*120}
        model=mock.Mock()
        model.collect_defined_terms.return_value=[1,2,3]
        model.get_float_value.return_value=.25
        model.get_integer_value.return_value=7
        model.get_bool_value.return_value=True
        with mock.patch.object(backend.Terms,'get_name',side_effect=names.__getitem__), \
                mock.patch.object(backend.Terms,'to_string',side_effect=AssertionError('pretty printer must not be called')), \
                mock.patch.object(backend.Terms,'is_real',side_effect=lambda term:term==1), \
                mock.patch.object(backend.Terms,'is_int',side_effect=lambda term:term==2), \
                mock.patch.object(backend.Terms,'is_bool',side_effect=lambda term:term==3):
            assignments=backend.YicesAssignment(model).get_assignments()
        self.assertEqual({variable.id for variable in assignments},set(names.values()))
        self.assertEqual(assignments[c.Real(names[1])].value,'0.25')
        self.assertEqual(assignments[c.Int(names[2])].value,'7')
        self.assertEqual(assignments[c.Bool(names[3])].value,'True')

    def test_native_yices_assignment_preserves_long_symbol_names(self):
        try:
            from stlmc.solver import yices as backend
        except (ImportError,OSError) as error:
            self.skipTest('optional Yices binding/native library unavailable: '+str(error))
        names={c.Real:'real_'+'r'*120,c.Int:'int_'+'i'*120,c.Bool:'bool_'+'b'*120}
        config=backend.Config()
        config.default_config_for_logic('QF_LIRA')
        context=backend.Context(config)
        model=None
        try:
            for kind,typ in [(c.Real,backend.Types.real_type()),(c.Int,backend.Types.int_type()),
                             (c.Bool,backend.Types.bool_type())]:
                term=backend.Terms.new_uninterpreted_term(typ)
                backend.Terms.set_name(term,names[kind])
                rhs=backend.Terms.true() if kind is c.Bool else backend.Terms.parse_rational('3')
                context.assert_formula(backend.Terms.eq(term,rhs))
            self.assertEqual(context.check_context(),backend.Status.SAT)
            model=backend.Model.from_context(context,1)
            assignments=backend.YicesAssignment(model).get_assignments()
            for kind,name in names.items():self.assertIn(kind(name),assignments)
        finally:
            if model is not None:model.dispose()
            context.dispose()
            config.dispose()

    def test_expression_formula_and_temporal_node_roundtrips(self):
        x,y=c.Real('x'),c.Real('y')
        interval=c.Interval(True,c.RealVal('1/3'),False,c.RealVal('2'))
        global_time=c.Interval(True,c.RealVal('0'),False,c.RealVal('inf'))
        nodes=[c.Int('n'),c.Bool('p'),c.RealVal('1e-30'),c.IntVal('42'),c.BoolVal('True')]
        nodes += [kind(x,y) for kind in (c.Add,c.Sub,c.Mul,c.Div,c.Pow,c.Gt,c.Geq,c.Lt,c.Leq,c.Eq,c.Neq,c.Implies)]
        nodes += [kind(x,y,is_range=True) for kind in (c.Gt,c.Geq,c.Lt,c.Leq,c.Eq)]
        nodes += [kind(x) for kind in (c.Neg,c.Sqrt,c.Sin,c.Cos,c.Tan,c.Arcsin,c.Arccos,c.Arctan,c.Not)]
        nodes += [c.And([c.Bool('p'),c.Bool('q')]),c.Or([c.Bool('p'),c.Bool('q')])]
        nodes += [kind(interval,global_time,c.Bool('p')) for kind in
                  (c.GloballyFormula,c.FinallyFormula,c.GloballyT1Formula,c.GloballyT2Formula)]
        nodes += [kind(interval,global_time,c.Bool('p'),c.Bool('q')) for kind in
                  (c.UntilFormula,c.ReleaseFormula)]
        nodes += [c.Reach(c.Bool('p'))]
        integral=c.Integral(0,[c.Real('x_0_t')],[c.Real('x_0_0')],c.Ode([x],[c.RealVal('1')]))
        nodes += [c.TimeBoundConst(x,y),integral,
                  c.Forall(0,c.Real('tau_1'),c.RealVal('0'),c.Geq(x,c.RealVal('0')),integral)]
        for node in nodes:
            with self.subTest(node=type(node).__name__):
                restored=self.roundtrip(example(node))[6]
                self.assertIs(type(restored),type(node))
                if isinstance(node,c.Reach):self.assertEqual(str(restored.formula),str(node.formula))
                else:self.assertEqual(str(restored),str(node))
                if hasattr(node,'local_time'):
                    self.assertEqual(restored.local_time,node.local_time)
                    self.assertEqual(restored.global_time,node.global_time)
                if hasattr(node,'is_range'):
                    self.assertEqual(restored.is_range,node.is_range)

    def test_pickle_is_rejected_without_executing_reduce(self):
        with tempfile.TemporaryDirectory() as directory:
            marker=Path(directory)/'executed'
            class Payload:
                def __reduce__(self):
                    return (eval,("__import__('pathlib').Path("+repr(str(marker))+").write_text('bad')",))
            path=Path(directory)/'malicious.counterexample'
            for payload in (pickle.dumps(example()),pickle.dumps(Payload()),gzip.compress(pickle.dumps(Payload()))):
                path.write_bytes(payload)
                with self.assertRaises(ValueError):codec.load_artifact(path)
                self.assertFalse(marker.exists())

    def test_executable_numeric_strings_are_rejected(self):
        for value in ("__import__('os').system('false')",'1;print(1)','sqrt(2)',"(lambda:1)()"):
            with self.subTest(value=value),tempfile.TemporaryDirectory() as directory:
                data=list(example())
                data[0]={c.Real('x'):c.RealVal(value)}
                with self.assertRaises(ValueError):
                    codec.dump_artifact(Path(directory)/'bad.counterexample',tuple(data))

    def test_generated_boolean_identifiers_roundtrip_without_becoming_code(self):
        data=list(example())
        names=['rho^{3,3}_'+'a'*64,'parEndrise^{1,3}_'+'b'*64,
               'chi^{1,1}_'+'c'*64,'parU^{2,4}_'+'d'*64]
        data[0].update({c.Bool(name):c.BoolVal('True') for name in names})
        restored=self.roundtrip(tuple(data))
        for name in names:self.assertEqual(restored[0][c.Bool(name)].value,'True')

    def test_solver_numeric_spellings_remain_exact(self):
        for literal in ('1/3','(/ 1 3)','(- (/ 1 3))','(1/3)',
                        '1.2345678901234567890123456789','-1e-30'):
            with self.subTest(literal=literal):
                data=list(example())
                data[0]={c.Real('x'):c.RealVal(literal)}
                restored=self.roundtrip(tuple(data))
                self.assertEqual(restored[0][c.Real('x')].value,literal)

    def test_json_nesting_limit_precedes_json_decode_and_ignores_string_brackets(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'deep.counterexample'
            raw=('['*(codec.MAX_DEPTH+2)+'0'+']'*(codec.MAX_DEPTH+2)).encode()
            path.write_bytes(gzip.compress(raw))
            with mock.patch.object(codec.json,'loads',side_effect=AssertionError('decoder must not run')):
                with self.assertRaises(ValueError):codec.load_artifact(path)
            codec.dump_artifact(path,example(),metadata={'text':'["escaped\\\"{]'*200})
            self.assertEqual(codec.load_artifact(path)[7],'f1')

    def test_executable_identifiers_and_cyclic_data_are_rejected(self):
        for name in ("__import__('os')",'x.__class__','x;print(1)','lambda:1'):
            data=list(example())
            data[0]={c.Real(name):c.RealVal('0')}
            with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
                with self.assertRaises(ValueError):
                    codec.dump_artifact(Path(directory)/'bad.counterexample',tuple(data))
        data=list(example())
        cycle=[]
        cycle.append(cycle)
        data[1]=cycle
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                codec.dump_artifact(Path(directory)/'bad.counterexample',tuple(data))

    def test_arbitrary_python_objects_are_not_serialized_by_class_name(self):
        class Unsupported:
            pass
        data=list(example())
        data[9]=Unsupported()
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                codec.dump_artifact(Path(directory)/'bad.counterexample',tuple(data))

    def test_hostile_numeric_values_are_rejected_on_read(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'bad.counterexample'
            codec.dump_artifact(path,example())
            document=json.loads(gzip.decompress(path.read_bytes()))
            def replace(value):
                if isinstance(value,dict):return {k:replace(v) for k,v in value.items()}
                if isinstance(value,list):return [replace(v) for v in value]
                return "__import__('os').system('false')" if value=='1e-20' else value
            altered=replace(document)
            self.assertNotEqual(altered,document)
            path.write_bytes(gzip.compress(json.dumps(altered).encode()))
            with self.assertRaises(ValueError):codec.load_artifact(path)

    def test_unknown_schema_and_operation_tags_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'bad.counterexample'
            codec.dump_artifact(path,example())
            valid=json.loads(gzip.decompress(path.read_bytes()))
            for key,value in [('format','arbitrary-import'),('schema_version',999)]:
                altered=dict(valid,**{key:value})
                path.write_bytes(gzip.compress(json.dumps(altered).encode()))
                with self.subTest(key=key),self.assertRaises(ValueError):codec.load_artifact(path)
            for tag in ('os.system','__import__','UnrecognizedOperator'):
                altered=dict(valid,data={'tag':tag,'module':'os','args':['false']})
                path.write_bytes(gzip.compress(json.dumps(altered).encode()))
                with self.subTest(tag=tag),self.assertRaises(ValueError):codec.load_artifact(path)

    def test_decompressed_size_depth_and_node_limits(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'limited.counterexample'
            codec.dump_artifact(path,example())
            original=path.read_bytes()
            for constant,limit in [('MAX_UNCOMPRESSED_BYTES',32),('MAX_DEPTH',2),('MAX_NODES',3)]:
                path.write_bytes(original)
                with self.subTest(limit=constant),mock.patch.object(codec,constant,limit):
                    with self.assertRaises(ValueError):codec.load_artifact(path)

    def test_truncated_gzip_and_nonfinite_json_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'broken.counterexample'
            codec.dump_artifact(path,example())
            original=path.read_bytes()
            for payload in (original[:10],gzip.compress(b'{"data": NaN}'),b'{}'):
                path.write_bytes(payload)
                with self.subTest(payload=payload[:10]),self.assertRaises(ValueError):codec.load_artifact(path)

    def test_outdated_pickle_is_rejected_without_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            source=Path(directory)/'old.counterexample'
            marker=Path(directory)/'executed'
            class Payload:
                def __reduce__(self):
                    return (eval,("__import__('pathlib').Path("+repr(str(marker))+").write_text('bad')",))
            source.write_bytes(pickle.dumps(Payload()))
            with self.assertRaisesRegex(ValueError, 'outdated.*regenerate'):
                codec.load_artifact(source)
            self.assertFalse(marker.exists())

    def test_legacy_nine_and_eleven_fields_are_unsupported(self):
        for length in (9,11):
            with self.subTest(length=length),tempfile.TemporaryDirectory() as directory:
                source=Path(directory)/'old.counterexample'
                original=example()[:length]
                original_bytes=pickle.dumps(original)
                source.write_bytes(original_bytes)
                with self.assertRaisesRegex(ValueError, 'outdated.*regenerate'):
                    codec.load_artifact(source)
                self.assertEqual(source.read_bytes(),original_bytes)

    def test_rejected_pickle_preserves_source(self):
        with tempfile.TemporaryDirectory() as directory:
            source=Path(directory)/'old.counterexample'
            original=pickle.dumps(example())
            source.write_bytes(original)
            with self.assertRaises(ValueError):
                codec.load_artifact(source)
            self.assertEqual(source.read_bytes(),original)


if __name__=='__main__':unittest.main()
