import Erdos883AdaptiveCertificate1508Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1508_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 11575794988913664188080968520266858325142176065903025861450241965304779916949919550638940495833908923557884469260569583812075264000849407308700286474944958613474839041976557273442839500636609624307815817574579968210172826707789169467309741220126606002282679053385203776
def adaptiveNumericSpans1508_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1508_0Chunk0].flatten
def adaptiveSpanEven1508_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 754 0 adaptiveNumericSpans1508_0)
def adaptiveSpanWhole1508_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1508_0)
theorem adaptiveSpanNumericCheck1508_0 : coreNumericSpansCheck 1472 6 480 1155 adaptiveNumericSpans1508_0 adaptiveRows1508 = true := by decide +kernel
theorem adaptiveSpanEvenCache1508_0 : adaptiveSpanEven1508_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1508_0 : adaptiveSpanEven1508_0.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1508_0 : adaptiveSpanEven1508_0.spans = coreEvenSpans 754 0 adaptiveNumericSpans1508_0 := by decide +kernel
theorem adaptiveSpanWholeCache1508_0 : adaptiveSpanWhole1508_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1508_0 : adaptiveSpanWhole1508_0.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1508_0 : adaptiveSpanWhole1508_0.spans = coreWholeSpans 0 adaptiveNumericSpans1508_0 := by decide +kernel
def adaptiveNumericSpans1508_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5682665953570223785630538842363823930470930382806029761174863133813537857668036746431411058763081423888576890249761079108432398293528963624695836964970696392387363281284913692800
def adaptiveNumericSpans1508_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1508_1Chunk0].flatten
def adaptiveSpanEven1508_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 754 0 adaptiveNumericSpans1508_1)
def adaptiveSpanWhole1508_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1508_1)
theorem adaptiveSpanNumericCheck1508_1 : coreNumericSpansCheck 1472 6 240 385 adaptiveNumericSpans1508_1 adaptiveRows1508 = true := by decide +kernel
theorem adaptiveSpanEvenCache1508_1 : adaptiveSpanEven1508_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1508_1 : adaptiveSpanEven1508_1.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1508_1 : adaptiveSpanEven1508_1.spans = coreEvenSpans 754 0 adaptiveNumericSpans1508_1 := by decide +kernel
theorem adaptiveSpanWholeCache1508_1 : adaptiveSpanWhole1508_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1508_1 : adaptiveSpanWhole1508_1.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1508_1 : adaptiveSpanWhole1508_1.spans = coreWholeSpans 0 adaptiveNumericSpans1508_1 := by decide +kernel
def adaptiveNumericSpans1508_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 11575794988913664188080968520266858325142176065903025861450241965304779916949919550638940495833908923557884469260569583811588270994784225592412419653716445950724226398562984897790198156568300790631513062092171192258253011392860730208078135725580958508923004377462997056
def adaptiveNumericSpans1508_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1508_2Chunk0].flatten
def adaptiveSpanEven1508_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 754 0 adaptiveNumericSpans1508_2)
def adaptiveSpanWhole1508_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1508_2)
theorem adaptiveSpanNumericCheck1508_2 : coreNumericSpansCheck 1472 6 720 1001 adaptiveNumericSpans1508_2 adaptiveRows1508 = true := by decide +kernel
theorem adaptiveSpanEvenCache1508_2 : adaptiveSpanEven1508_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1508_2 : adaptiveSpanEven1508_2.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1508_2 : adaptiveSpanEven1508_2.spans = coreEvenSpans 754 0 adaptiveNumericSpans1508_2 := by decide +kernel
theorem adaptiveSpanWholeCache1508_2 : adaptiveSpanWhole1508_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1508_2 : adaptiveSpanWhole1508_2.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1508_2 : adaptiveSpanWhole1508_2.spans = coreWholeSpans 0 adaptiveNumericSpans1508_2 := by decide +kernel
def adaptiveNumericSpans1508_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 14674063465815336518387654287427121287206913609185772507439889876771863524995847247299167154777926813426829744869612185879293004970189383235924808239314154230952152132435890270202260470844055165617642629877197070930162738147839563378889905835699486025572327989277969333517908621981978950572082987072
def adaptiveNumericSpans1508_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1508_3Chunk0].flatten
def adaptiveSpanEven1508_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 754 0 adaptiveNumericSpans1508_3)
def adaptiveSpanWhole1508_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1508_3)
theorem adaptiveSpanNumericCheck1508_3 : coreNumericSpansCheck 1472 6 120 143 adaptiveNumericSpans1508_3 adaptiveRows1508 = true := by decide +kernel
theorem adaptiveSpanEvenCache1508_3 : adaptiveSpanEven1508_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1508_3 : adaptiveSpanEven1508_3.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1508_3 : adaptiveSpanEven1508_3.spans = coreEvenSpans 754 0 adaptiveNumericSpans1508_3 := by decide +kernel
theorem adaptiveSpanWholeCache1508_3 : adaptiveSpanWhole1508_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1508_3 : adaptiveSpanWhole1508_3.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1508_3 : adaptiveSpanWhole1508_3.spans = coreWholeSpans 0 adaptiveNumericSpans1508_3 := by decide +kernel
def adaptiveNumericSpans1508_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 29891595198881356718837593077391747662896646197966265602755313447216432807157528621538062215152146314856377620607906058531311072361923201718772709634346686427734350213716430464927603532944603831637403565469573361826063329396441505254602120355566069522888157616280765368604506566748523957034071572067502263783842323237057522411707024150726788459571825773865097278084689282739103899020427328
def adaptiveNumericSpans1508_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1508_4Chunk0].flatten
def adaptiveSpanEven1508_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 754 0 adaptiveNumericSpans1508_4)
def adaptiveSpanWhole1508_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1508_4)
theorem adaptiveSpanNumericCheck1508_4 : coreNumericSpansCheck 1472 6 192 221 adaptiveNumericSpans1508_4 adaptiveRows1508 = true := by decide +kernel
theorem adaptiveSpanEvenCache1508_4 : adaptiveSpanEven1508_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1508_4 : adaptiveSpanEven1508_4.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1508_4 : adaptiveSpanEven1508_4.spans = coreEvenSpans 754 0 adaptiveNumericSpans1508_4 := by decide +kernel
theorem adaptiveSpanWholeCache1508_4 : adaptiveSpanWhole1508_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1508_4 : adaptiveSpanWhole1508_4.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1508_4 : adaptiveSpanWhole1508_4.spans = coreWholeSpans 0 adaptiveNumericSpans1508_4 := by decide +kernel
def adaptiveNumericSpans1508_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 15 48033941528671830830782213519837472081338522427220123745575811768726034920163595114099636088512623231559740844419524990488672667737448722837698870904959739109526434931562361314980367498190585577833219355701716123534978377103698993057060498528522741687420192457824341198393845843078288852643671496671952468867270505449050310416914784139527414419043764908846656211518835493184476059152825357828486804534583942447605940758092362445611905362858474471488
def adaptiveNumericSpans1508_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1508_5Chunk0].flatten
def adaptiveSpanEven1508_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 754 0 adaptiveNumericSpans1508_5)
def adaptiveSpanWhole1508_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1508_5)
theorem adaptiveSpanNumericCheck1508_5 : coreNumericSpansCheck 1472 6 288 323 adaptiveNumericSpans1508_5 adaptiveRows1508 = true := by decide +kernel
theorem adaptiveSpanEvenCache1508_5 : adaptiveSpanEven1508_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1508_5 : adaptiveSpanEven1508_5.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1508_5 : adaptiveSpanEven1508_5.spans = coreEvenSpans 754 0 adaptiveNumericSpans1508_5 := by decide +kernel
theorem adaptiveSpanWholeCache1508_5 : adaptiveSpanWhole1508_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1508_5 : adaptiveSpanWhole1508_5.domainCheck 754 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1508_5 : adaptiveSpanWhole1508_5.spans = coreWholeSpans 0 adaptiveNumericSpans1508_5 := by decide +kernel
end Erdos883Verified
