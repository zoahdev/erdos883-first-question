import Erdos883AdaptiveCertificate2138Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2138_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 20968787136429944438045734464388781068242529745211102827934205759413175852425452215567394825819455217020881019645189787398816843783774215129817695256749754033839456515564192856560660596470113003659785353339339768332073098515305405992414709502111470363493433239312601163584021243786562011544508432512
def adaptiveNumericSpans2138_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2138_0Chunk0].flatten
def adaptiveSpanEven2138_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1069 0 adaptiveNumericSpans2138_0)
def adaptiveSpanWhole2138_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2138_0)
theorem adaptiveSpanNumericCheck2138_0 : coreNumericSpansCheck 2086 6 480 1155 adaptiveNumericSpans2138_0 adaptiveRows2138 = true := by decide +kernel
theorem adaptiveSpanEvenCache2138_0 : adaptiveSpanEven2138_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2138_0 : adaptiveSpanEven2138_0.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2138_0 : adaptiveSpanEven2138_0.spans = coreEvenSpans 1069 0 adaptiveNumericSpans2138_0 := by decide +kernel
theorem adaptiveSpanWholeCache2138_0 : adaptiveSpanWhole2138_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2138_0 : adaptiveSpanWhole2138_0.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2138_0 : adaptiveSpanWhole2138_0.spans = coreWholeSpans 0 adaptiveNumericSpans2138_0 := by decide +kernel
def adaptiveNumericSpans2138_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 16541456401830833940813086440672067053503298102323015182080847386717963488603032158910798414120930140190450128003279347511916493852454550825867220737859154267529202738712280409250946580104130910652557743068295620565481289994856396705595116262860999009795847914468147328
def adaptiveNumericSpans2138_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2138_1Chunk0].flatten
def adaptiveSpanEven2138_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1069 0 adaptiveNumericSpans2138_1)
def adaptiveSpanWhole2138_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2138_1)
theorem adaptiveSpanNumericCheck2138_1 : coreNumericSpansCheck 2086 6 240 385 adaptiveNumericSpans2138_1 adaptiveRows2138 = true := by decide +kernel
theorem adaptiveSpanEvenCache2138_1 : adaptiveSpanEven2138_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2138_1 : adaptiveSpanEven2138_1.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2138_1 : adaptiveSpanEven2138_1.spans = coreEvenSpans 1069 0 adaptiveNumericSpans2138_1 := by decide +kernel
theorem adaptiveSpanWholeCache2138_1 : adaptiveSpanWhole2138_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2138_1 : adaptiveSpanWhole2138_1.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2138_1 : adaptiveSpanWhole2138_1.spans = coreWholeSpans 0 adaptiveNumericSpans2138_1 := by decide +kernel
def adaptiveNumericSpans2138_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 16541456401830833940813086440672067053503298102323015182080847386717963488603032158910798414120930140190450128003279347511916493852454550825867220737859210907941292566769434059105764455238693604976818844758753675395692084291294806594095466166737320041609087705812041856
def adaptiveNumericSpans2138_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2138_2Chunk0].flatten
def adaptiveSpanEven2138_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1069 0 adaptiveNumericSpans2138_2)
def adaptiveSpanWhole2138_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2138_2)
theorem adaptiveSpanNumericCheck2138_2 : coreNumericSpansCheck 2086 6 720 1001 adaptiveNumericSpans2138_2 adaptiveRows2138 = true := by decide +kernel
theorem adaptiveSpanEvenCache2138_2 : adaptiveSpanEven2138_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2138_2 : adaptiveSpanEven2138_2.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2138_2 : adaptiveSpanEven2138_2.spans = coreEvenSpans 1069 0 adaptiveNumericSpans2138_2 := by decide +kernel
theorem adaptiveSpanWholeCache2138_2 : adaptiveSpanWhole2138_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2138_2 : adaptiveSpanWhole2138_2.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2138_2 : adaptiveSpanWhole2138_2.spans = coreWholeSpans 0 adaptiveNumericSpans2138_2 := by decide +kernel
def adaptiveNumericSpans2138_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 20968787136429944438045734464388781068242529745211102827934205759413175852425452215567394825819455217020881019645189787399034494642741495014794095338010821568745011584414156208071353236417156441305536327699815177300691737164689199436978089898075255840330551502171272715147348113408506469987762831488
def adaptiveNumericSpans2138_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2138_3Chunk0].flatten
def adaptiveSpanEven2138_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1069 0 adaptiveNumericSpans2138_3)
def adaptiveSpanWhole2138_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2138_3)
theorem adaptiveSpanNumericCheck2138_3 : coreNumericSpansCheck 2086 6 120 143 adaptiveNumericSpans2138_3 adaptiveRows2138 = true := by decide +kernel
theorem adaptiveSpanEvenCache2138_3 : adaptiveSpanEven2138_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2138_3 : adaptiveSpanEven2138_3.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2138_3 : adaptiveSpanEven2138_3.spans = coreEvenSpans 1069 0 adaptiveNumericSpans2138_3 := by decide +kernel
theorem adaptiveSpanWholeCache2138_3 : adaptiveSpanWhole2138_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2138_3 : adaptiveSpanWhole2138_3.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2138_3 : adaptiveSpanWhole2138_3.spans = coreWholeSpans 0 adaptiveNumericSpans2138_3 := by decide +kernel
def adaptiveNumericSpans2138_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 33695541791497808016546633301308508827140472277993861000486236476887784974309104190924265400542655109540937215080278909017480631720876275494410619739099366763981730193509423494665285351213543379304108414727768176313386509309852537516303322650501441126991954178973543235290800118695982558018559972198471350106555343014643776913317746561060465712299193776734336
def adaptiveNumericSpans2138_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans2138_4Chunk0].flatten
def adaptiveSpanEven2138_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 1069 0 adaptiveNumericSpans2138_4)
def adaptiveSpanWhole2138_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2138_4)
theorem adaptiveSpanNumericCheck2138_4 : coreNumericSpansCheck 2086 6 192 221 adaptiveNumericSpans2138_4 adaptiveRows2138 = true := by decide +kernel
theorem adaptiveSpanEvenCache2138_4 : adaptiveSpanEven2138_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2138_4 : adaptiveSpanEven2138_4.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2138_4 : adaptiveSpanEven2138_4.spans = coreEvenSpans 1069 0 adaptiveNumericSpans2138_4 := by decide +kernel
theorem adaptiveSpanWholeCache2138_4 : adaptiveSpanWhole2138_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2138_4 : adaptiveSpanWhole2138_4.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2138_4 : adaptiveSpanWhole2138_4.spans = coreWholeSpans 0 adaptiveNumericSpans2138_4 := by decide +kernel
def adaptiveNumericSpans2138_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 26581095599553394663114513402293366165485690465105896394216275231825777225533113385775307478367680553315569571947117912872948178628640872808497679226373955641518325698486685350922402654031924452705746148847067289945392642575168042846517420155770780782911470805926023711528205018812489377006125488244219502774604583529138498830464
def adaptiveNumericSpans2138_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans2138_5Chunk0].flatten
def adaptiveSpanEven2138_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 1069 0 adaptiveNumericSpans2138_5)
def adaptiveSpanWhole2138_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2138_5)
theorem adaptiveSpanNumericCheck2138_5 : coreNumericSpansCheck 2086 6 288 323 adaptiveNumericSpans2138_5 adaptiveRows2138 = true := by decide +kernel
theorem adaptiveSpanEvenCache2138_5 : adaptiveSpanEven2138_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2138_5 : adaptiveSpanEven2138_5.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2138_5 : adaptiveSpanEven2138_5.spans = coreEvenSpans 1069 0 adaptiveNumericSpans2138_5 := by decide +kernel
theorem adaptiveSpanWholeCache2138_5 : adaptiveSpanWhole2138_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2138_5 : adaptiveSpanWhole2138_5.domainCheck 1069 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2138_5 : adaptiveSpanWhole2138_5.spans = coreWholeSpans 0 adaptiveNumericSpans2138_5 := by decide +kernel
end Erdos883Verified
