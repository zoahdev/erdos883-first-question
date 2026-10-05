import Erdos883AdaptiveCertificate2540Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2540_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 31244445541750733989899123191116821831914627160278686220391331208507605275997516765577082985433342695485062707099737055473161565009825402566101789544345261064602150414934902507586044785546113252657229035638060386136535190988496219699119973951169528535566606056963058363989361652833277311992038504357448502934883452652584307785856
def adaptiveNumericSpans2540_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2540_0Chunk0].flatten
def adaptiveSpanEven2540_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1270 0 adaptiveNumericSpans2540_0)
def adaptiveSpanWhole2540_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2540_0)
theorem adaptiveSpanNumericCheck2540_0 : coreNumericSpansCheck 2479 7 480 1155 adaptiveNumericSpans2540_0 adaptiveRows2540 = true := by decide +kernel
theorem adaptiveSpanEvenCache2540_0 : adaptiveSpanEven2540_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2540_0 : adaptiveSpanEven2540_0.domainCheck 1270 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2540_0 : adaptiveSpanEven2540_0.spans = coreEvenSpans 1270 0 adaptiveNumericSpans2540_0 := by decide +kernel
theorem adaptiveSpanWholeCache2540_0 : adaptiveSpanWhole2540_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2540_0 : adaptiveSpanWhole2540_0.domainCheck 1270 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2540_0 : adaptiveSpanWhole2540_0.spans = coreWholeSpans 0 adaptiveNumericSpans2540_0 := by decide +kernel
def adaptiveNumericSpans2540_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 24647521593194090617956846494394537261773423832672348379777729996411524539632469469711365656899464043283561135820646623148786994244100498224185325864660735997513334010778072809697763487447894680611826910281751800469859092005860232084903695489239779859719294865813233074899454976069500665662692917376
def adaptiveNumericSpans2540_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2540_1Chunk0].flatten
def adaptiveSpanEven2540_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1270 0 adaptiveNumericSpans2540_1)
def adaptiveSpanWhole2540_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2540_1)
theorem adaptiveSpanNumericCheck2540_1 : coreNumericSpansCheck 2479 7 240 385 adaptiveNumericSpans2540_1 adaptiveRows2540 = true := by decide +kernel
theorem adaptiveSpanEvenCache2540_1 : adaptiveSpanEven2540_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2540_1 : adaptiveSpanEven2540_1.domainCheck 1270 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2540_1 : adaptiveSpanEven2540_1.spans = coreEvenSpans 1270 0 adaptiveNumericSpans2540_1 := by decide +kernel
theorem adaptiveSpanWholeCache2540_1 : adaptiveSpanWhole2540_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2540_1 : adaptiveSpanWhole2540_1.domainCheck 1270 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2540_1 : adaptiveSpanWhole2540_1.spans = coreWholeSpans 0 adaptiveNumericSpans2540_1 := by decide +kernel
end Erdos883Verified
