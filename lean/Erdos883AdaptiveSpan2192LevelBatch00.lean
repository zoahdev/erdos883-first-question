import Erdos883AdaptiveCertificate2192Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2192_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 21510378616201777406919350512377687870278281730209078515463348889233597857915388787004394804403576983054732563608177547224969104891812958470923063679297678644380878129871775616882736223651894713977397137758383899816878291748862784410898728298419730145166988695285825820136062585105120093468140503168
def adaptiveNumericSpans2192_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2192_0Chunk0].flatten
def adaptiveSpanEven2192_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1096 0 adaptiveNumericSpans2192_0)
def adaptiveSpanWhole2192_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2192_0)
theorem adaptiveSpanNumericCheck2192_0 : coreNumericSpansCheck 2139 6 480 1155 adaptiveNumericSpans2192_0 adaptiveRows2192 = true := by decide +kernel
theorem adaptiveSpanEvenCache2192_0 : adaptiveSpanEven2192_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2192_0 : adaptiveSpanEven2192_0.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2192_0 : adaptiveSpanEven2192_0.spans = coreEvenSpans 1096 0 adaptiveNumericSpans2192_0 := by decide +kernel
theorem adaptiveSpanWholeCache2192_0 : adaptiveSpanWhole2192_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2192_0 : adaptiveSpanWhole2192_0.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2192_0 : adaptiveSpanWhole2192_0.spans = coreWholeSpans 0 adaptiveNumericSpans2192_0 := by decide +kernel
def adaptiveNumericSpans2192_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 16968696746823629400887546502456224131242705064726468137048985205862479598387577118339849063829617089226867390397923859671052701971302974199972431408738875354390363654137166518051223117355172149065215625905270729703571382539496092850690246302563015734637168834576908416
def adaptiveNumericSpans2192_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2192_1Chunk0].flatten
def adaptiveSpanEven2192_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1096 0 adaptiveNumericSpans2192_1)
def adaptiveSpanWhole2192_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2192_1)
theorem adaptiveSpanNumericCheck2192_1 : coreNumericSpansCheck 2139 6 240 385 adaptiveNumericSpans2192_1 adaptiveRows2192 = true := by decide +kernel
theorem adaptiveSpanEvenCache2192_1 : adaptiveSpanEven2192_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2192_1 : adaptiveSpanEven2192_1.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2192_1 : adaptiveSpanEven2192_1.spans = coreEvenSpans 1096 0 adaptiveNumericSpans2192_1 := by decide +kernel
theorem adaptiveSpanWholeCache2192_1 : adaptiveSpanWhole2192_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2192_1 : adaptiveSpanWhole2192_1.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2192_1 : adaptiveSpanWhole2192_1.spans = coreWholeSpans 0 adaptiveNumericSpans2192_1 := by decide +kernel
def adaptiveNumericSpans2192_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 27267644363964653688490973388861210202525287671685219976479942508304901768474857708396042800038747639194393536543670443257010481493001138778761113725089614825128629510549695190381370990476291659422631862453083921603559935086093842369236600843938219262899197898896184371293581386620258765670377534613742259726026309431512369463424
def adaptiveNumericSpans2192_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2192_2Chunk0].flatten
def adaptiveSpanEven2192_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1096 0 adaptiveNumericSpans2192_2)
def adaptiveSpanWhole2192_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2192_2)
theorem adaptiveSpanNumericCheck2192_2 : coreNumericSpansCheck 2139 6 720 1001 adaptiveNumericSpans2192_2 adaptiveRows2192 = true := by decide +kernel
theorem adaptiveSpanEvenCache2192_2 : adaptiveSpanEven2192_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2192_2 : adaptiveSpanEven2192_2.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2192_2 : adaptiveSpanEven2192_2.spans = coreEvenSpans 1096 0 adaptiveNumericSpans2192_2 := by decide +kernel
theorem adaptiveSpanWholeCache2192_2 : adaptiveSpanWhole2192_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2192_2 : adaptiveSpanWhole2192_2.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2192_2 : adaptiveSpanWhole2192_2.spans = coreWholeSpans 0 adaptiveNumericSpans2192_2 := by decide +kernel
def adaptiveNumericSpans2192_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 27267644363964653688490973388861210202525287671685219976479942508304901768474857708396042800038747639194393536543670443257988690976525437800280961406104190503931210098764599837780842351615432530571889210400288549698914238205932732765464066618461388025332611159663108454795245248634794423269965684989283008885057110079472670867584
def adaptiveNumericSpans2192_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2192_3Chunk0].flatten
def adaptiveSpanEven2192_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1096 0 adaptiveNumericSpans2192_3)
def adaptiveSpanWhole2192_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2192_3)
theorem adaptiveSpanNumericCheck2192_3 : coreNumericSpansCheck 2139 6 120 143 adaptiveNumericSpans2192_3 adaptiveRows2192 = true := by decide +kernel
theorem adaptiveSpanEvenCache2192_3 : adaptiveSpanEven2192_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2192_3 : adaptiveSpanEven2192_3.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2192_3 : adaptiveSpanEven2192_3.spans = coreEvenSpans 1096 0 adaptiveNumericSpans2192_3 := by decide +kernel
theorem adaptiveSpanWholeCache2192_3 : adaptiveSpanWhole2192_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2192_3 : adaptiveSpanWhole2192_3.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2192_3 : adaptiveSpanWhole2192_3.spans = coreWholeSpans 0 adaptiveNumericSpans2192_3 := by decide +kernel
def adaptiveNumericSpans2192_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 55545172559290285200899587961564323761626582718464141774817480432898983560984783733804100076036111055998740463507747093904415649902413112267062995097036360325654681454100150975346376804820085839105875292084349931198490329120788656141336653190344885310124808973540544977488262859157123058345795768960039230689507411921696385606869175345138347159701241980363391673174297083352300336982277723837097390827905599832640716928
def adaptiveNumericSpans2192_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans2192_4Chunk0].flatten
def adaptiveSpanEven2192_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 1096 0 adaptiveNumericSpans2192_4)
def adaptiveSpanWhole2192_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2192_4)
theorem adaptiveSpanNumericCheck2192_4 : coreNumericSpansCheck 2139 6 192 221 adaptiveNumericSpans2192_4 adaptiveRows2192 = true := by decide +kernel
theorem adaptiveSpanEvenCache2192_4 : adaptiveSpanEven2192_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2192_4 : adaptiveSpanEven2192_4.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2192_4 : adaptiveSpanEven2192_4.spans = coreEvenSpans 1096 0 adaptiveNumericSpans2192_4 := by decide +kernel
theorem adaptiveSpanWholeCache2192_4 : adaptiveSpanWhole2192_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2192_4 : adaptiveSpanWhole2192_4.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2192_4 : adaptiveSpanWhole2192_4.spans = coreWholeSpans 0 adaptiveNumericSpans2192_4 := by decide +kernel
def adaptiveNumericSpans2192_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 27267644363964653688490973388861210202525287671685219976479942508304901768474857708396042800038747639194393536543670443257813114917344496408735527421406760635598907960671296722114425599900420286623604162358238290802261867317656361768675953563955681069120270091809687972651754550202799861558240299872142431550387300681087029608576
def adaptiveNumericSpans2192_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans2192_5Chunk0].flatten
def adaptiveSpanEven2192_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 1096 0 adaptiveNumericSpans2192_5)
def adaptiveSpanWhole2192_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2192_5)
theorem adaptiveSpanNumericCheck2192_5 : coreNumericSpansCheck 2139 6 288 323 adaptiveNumericSpans2192_5 adaptiveRows2192 = true := by decide +kernel
theorem adaptiveSpanEvenCache2192_5 : adaptiveSpanEven2192_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2192_5 : adaptiveSpanEven2192_5.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2192_5 : adaptiveSpanEven2192_5.spans = coreEvenSpans 1096 0 adaptiveNumericSpans2192_5 := by decide +kernel
theorem adaptiveSpanWholeCache2192_5 : adaptiveSpanWhole2192_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2192_5 : adaptiveSpanWhole2192_5.domainCheck 1096 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2192_5 : adaptiveSpanWhole2192_5.spans = coreWholeSpans 0 adaptiveNumericSpans2192_5 := by decide +kernel
end Erdos883Verified
