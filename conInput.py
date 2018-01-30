
testcase = [
        "([] (0.0,1.0) p)",
        "(<> (3.682309599907781,8.39356728634411] p5)",
        "([] (1.5123960886106453,1.5575072539544195) p4)",
        "(<> [2.270425748990146,2.564170326689469] p5)",
        "(~ p5)",
        "(p U [0.0,4.0) q)",
        "(<> [0.04506359228341472,3.646640163616085) (~ p3))",
        "((<> [1.0,2.0] p) U (0.5,3.0) p)",
        "(p4 R (3.456002457918444,3.9719680958123584] ([] [2.378898151260885,3.356899811628598] p4))",
        "(p5 /\ (<> (3.949620756503574,7.73996810508705) p5))",
        "(false \/ (~ p5))",
        "(p1 R [1.8678739817440382,3.784139823201288) ([] (4.046789219270622,5.246931335125865] p3))",
        "((<> [0.1679683742985938,1.8407821725714846) false) \/ ([] (1.5224970714528556,4.883993462166918) false))",
        "(~ (<> [4.957918129133757,7.473679439826357] ([] [2.682575959924987,5.363016136040974] p5)))",
        "([] (3.4101382145727026,4.480878693817997) (<> [0.25861298980080216,0.9673648220184317] (<> (0.051786896378698266,2.197991073421335] false)))",
        "([] [0.0,1.0] (p -> (<> [1.0,2.0] q)))",
        "(p5 \/ (<> (2.1910189100405457,2.9572426925964854] (~ p1)))",
        "(<> (1.1732969181787611,1.3200778457209261] (p2 -> (<> [2.469803413631651,5.62043370627957] p3)))",
        "([] [0.0,1.0] (p -> (q U [1.0,2.0] r)))",
        "((false R (0.40624601023155626,2.693242117282285] (<> [2.574312732813277,6.643532173427319) false)) -> (~ p1))",
        "((~ false) -> (false -> (<> (4.776300371223462,6.853413612517303) p2)))",
        "(<> (1.2246235748862704,3.1251110185373663] (~ (~ (<> [1.821517857758617,6.50804319361931) p1))))",
        "(<> (0.0,0.4) ([] [0.0,1.0] (p -> (q U [1.0,2.0] r))))",
        "([] [2.7898570509996223,6.276387777521548] (p2 R [4.208479194962818,6.63752412444488] (p2 /\ (~ p5))))",
        "(~ ((~ (~ p3)) /\ ([] (4.1827516674829734,5.914916330692419] false)))",
        "(<> (1.8891937845921176,3.9087583908194103) (p2 U (0.7941519099608224,2.250469027820925] (p3 -> ([] (3.2183292560244974,6.298257713042361] p5))))",
        "(~ ((false \/ (<> (2.117337146157235,5.915372528550228] false)) /\ (~ p1)))",
        "((~ (p4 /\ ([] [4.667811750910834,6.158593486955159] false))) -> ([] (0.9633280214963974,1.563989036132144) false))",
        "((~ ([] [4.601361981462718,8.762455813368184] (~ p1))) /\ (false U (1.1164107105590433,5.950634456282197) (<> [4.322650610628099,5.801278366320982) p2)))",
        "((~ (~ (<> (0.28388234877078755,2.6789539573170322) p5))) -> ((~ false) R [4.006454476673352,6.745424262017857) ([] [2.9013878463547087,6.350732755116731] p4)))",
        "(([] (4.145802930329407,4.431796996565416) (~ false)) R [2.6733537153073037,4.895400691491595] (p2 -> (false R [0.9286668402381226,1.918688270746471) (<> (2.1252599528226703,4.756834124572119] p3))))",
        "((p5 U [0.046520187593479534,2.2760151420079646] (~ p5)) -> ([] (1.7630659393922044,3.7102729990273007) (p2 \/ (<> [0.402869795704649,4.259341270175079) p3))))",
        "(~ (<> (4.108546324610599,7.985470634218853] ([] [2.186195608016641,3.024240655301906) ([] [0.1714504746527873,5.098924509854656] (~ p2)))))",
        "([] [0.0,1.0] (p -> (<> [1.0,2.0] (q /\ ([] [3.0,3.0] r)))))",
        "((<> (1.3469446264729779,1.7149975500325971] false) \/ ([] [4.767722089301461,7.260123139012579] (~ (false \/ (<> (3.5818548240569474,8.387840613011702] p1)))))",
        "(<> [1.67447224444969,3.2451772053333037] ((<> [0.9312843228519746,2.427555436388668) ([] (3.3494667590632514,4.207940411386712] false)) R (0.2282319849474418,1.167709518349635) (<> [4.5578771194672525,6.25108374297218] (<> [1.2911518311027286,1.7048899056594995) (<> [3.654938974443147,7.303917911409463) false)))))",
        "([] [0.0,1.0] (p -> ((~ r) U [1.0,2.0] (q /\ ([] [3.0,4.0] r)))))",
        "(p3 /\ ([] [0.5939261009816332,5.002885052820904] (false \/ p4 \/ (p3 -> ([] (3.9689026529661025,8.54206248540575) p5)))))",
        "((<> (1.0,2.0) r) U [0.0,1.0] (p -> ((~ s) U [1.0,2.0] (q /\ ([] [3.0,4.0] r)))))",
        "(([] (4.834803157293738,6.430718409786307] ([] [2.836376781262575,4.862365007849716) false)) -> ((~ (p1 U (2.0130018458987835,6.539617076688387) ([] (2.1658311976028783,6.429430940811768) p1))) R (1.3867607850930903,3.3617150123976574] (<> (3.485607289331949,4.592677261309559) p5)))",
        "([] (1.3560480289148857,2.400994256271123] ((~ ([] (3.6512079349944777,8.355212880912823] (~ p4))) R [1.8882718832425565,4.582173687424509] (<> (4.7152405547022695,5.492771436009355) (([] [0.20914509654008706,4.612507328700136) false) /\ (<> [1.4979885214069188,4.6721169313988895) false)))))",
        "(((<> (4.133717263698839,7.830014999939204) (~ (<> (2.2471972227232735,4.992672861353395) p1))) U [0.6017455974511948,3.846748315540292] (<> (0.8651237794268424,2.6574700697576144] p4)) \/ ((~ p4) R (1.6616874686277139,4.38332763612589) (<> [1.4853270085805992,3.392192465220995] p3)))",
        "(~ ((false -> (<> (0.9414744174357348,4.234480975414261) p5)) R [2.871046850537786,6.4023903822522366] (([] [4.862340100048243,5.680861123194551) p4) R (4.633927152701487,8.705014530435975] (false -> ([] (4.397099156157545,4.782627193021343] false)))))",
        "(([] (1.0,2.0) (<> (1.0,2.0) (~ r))) U [0.0,1.0] ((~ p) -> (s U [1.0,2.0] (q /\ ([] [3.0,4.0] r)))))",
        "(~ (<> [0.5336632341235509,4.928140652312167] (~ (([] (4.474727623620856,8.969450890924097] (<> [3.902873419655175,4.867351345436625] p2)) -> (<> (4.442631784527777,6.545925938354573] p3)))))",
        "((<> (0.20721112865259683,2.151436984645419) p4) /\ (~ (<> [2.253461643540642,7.08666625375245] (([] [4.638417056936046,8.376869198819625] p1) -> ([] (3.5428577061631543,6.825172729344348) (<> (4.356757929706584,6.143421498909607] p2))))))",
        "(~ (p4 \/ ([] [4.890552090235126,6.7387334911964185) (<> (0.5961446586536878,2.640417996173774] p1)) \/ (~ (~ (<> [0.7239959485956288,1.4724974574142113) ([] [0.22094627839946035,3.897547505562189] p4))))))",
        "(<> [2.4205393766765164,4.0823581884904065) ((p1 -> (~ false)) /\ (p4 \/ (p4 /\ (<> [3.96336194463578,8.44436369868475] ([] (1.2462028702438603,2.6924315609388754) p2))))))",
        "(~ ([] [4.692152869911323,8.57846846236703] (p3 R [3.0569869931403466,4.736450194281179] (false /\ (<> [0.19923853935822466,1.7771253868983083] (p3 R (3.5220244834400316,5.1744360889786165) (<> (0.9371792520313488,3.4529161529982133) false)))))))",
        "(false R (0.4203887053452027,5.36194584832577] (<> [4.495847750743349,5.130456952330768] ([] (1.635983927324809,3.0288510509187483) (([] [0.8082481558745502,0.9267425091379716) false) -> (<> [3.2952886932668517,7.406406259421054) (~ (~ false)))))))",
"(~ (~ (([] (3.4136442065022776,6.668534279332581] (~ (false \/ false \/ (<> (0.7585896620612481,0.9065522654176061) p3)))) \/ (<> (2.9167469565823216,7.07459728020659] p1))))"
]

