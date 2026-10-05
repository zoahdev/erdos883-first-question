import Erdos883AdaptiveCertificate2540Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2540_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 24647521593194090617956846494394537261773423832672348379777729996411524539632469469711365656899464043283561135820646623148786994244100498224185325864660735997513334010778072809697763706621659832472342351079167384337890715892160397637634727978326934775589164241706736849608004406768360851603516817536
def adaptiveNumericSpans2540_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2540_2Chunk0].flatten
def adaptiveSpanEven2540_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1270 0 adaptiveNumericSpans2540_2)
def adaptiveSpanWhole2540_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2540_2)
theorem adaptiveSpanNumericCheck2540_2 : coreNumericSpansCheck 2479 7 720 1001 adaptiveNumericSpans2540_2 adaptiveRows2540 = true := by decide +kernel
theorem adaptiveSpanEvenCache2540_2 : adaptiveSpanEven2540_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2540_2 : adaptiveSpanEven2540_2.domainCheck 1270 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2540_2 : adaptiveSpanEven2540_2.spans = coreEvenSpans 1270 0 adaptiveNumericSpans2540_2 := by decide +kernel
theorem adaptiveSpanWholeCache2540_2 : adaptiveSpanWhole2540_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2540_2 : adaptiveSpanWhole2540_2.domainCheck 1270 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2540_2 : adaptiveSpanWhole2540_2.spans = coreWholeSpans 0 adaptiveNumericSpans2540_2 := by decide +kernel
def adaptiveNumericSpans2540_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 24647521593194090617956846494394537261773423832672348379777729996411524539632469469711365656899464043283561135820646623148786994244100498224185325864660754728013567300975605516752212844698128650383766008063896626002584180944323872055275797779906104735193117171636153682687274610410144213835498651776
def adaptiveNumericSpans2540_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2540_3Chunk0].flatten
def adaptiveSpanEven2540_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1270 0 adaptiveNumericSpans2540_3)
def adaptiveSpanWhole2540_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2540_3)
theorem adaptiveSpanNumericCheck2540_3 : coreNumericSpansCheck 2479 7 1920 2431 adaptiveNumericSpans2540_3 adaptiveRows2540 = true := by decide +kernel
theorem adaptiveSpanEvenCache2540_3 : adaptiveSpanEven2540_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2540_3 : adaptiveSpanEven2540_3.domainCheck 1270 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2540_3 : adaptiveSpanEven2540_3.spans = coreEvenSpans 1270 0 adaptiveNumericSpans2540_3 := by decide +kernel
theorem adaptiveSpanWholeCache2540_3 : adaptiveSpanWhole2540_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2540_3 : adaptiveSpanWhole2540_3.domainCheck 1270 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2540_3 : adaptiveSpanWhole2540_3.spans = coreWholeSpans 0 adaptiveNumericSpans2540_3 := by decide +kernel
end Erdos883Verified
