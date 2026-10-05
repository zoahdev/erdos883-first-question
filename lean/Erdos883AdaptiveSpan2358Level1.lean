import Erdos883AdaptiveCertificate2358Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2358_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 22838810403753417808093757072779857403453235808698623658180640045236504097994494554194940364983001600284712993649498573813633684320015886292646873490568501756700963903898079585091645274568853116311049053454597732830449799266188767543767586763794371171685012797781510620071640344337705000360738816128
def adaptiveNumericSpans2358_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2358_1Chunk0].flatten
def adaptiveSpanEven2358_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1179 0 adaptiveNumericSpans2358_1)
def adaptiveSpanWhole2358_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2358_1)
theorem adaptiveSpanNumericCheck2358_1 : coreNumericSpansCheck 2301 7 240 385 adaptiveNumericSpans2358_1 adaptiveRows2358 = true := by decide +kernel
theorem adaptiveSpanEvenCache2358_1 : adaptiveSpanEven2358_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2358_1 : adaptiveSpanEven2358_1.domainCheck 1179 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2358_1 : adaptiveSpanEven2358_1.spans = coreEvenSpans 1179 0 adaptiveNumericSpans2358_1 := by decide +kernel
theorem adaptiveSpanWholeCache2358_1 : adaptiveSpanWhole2358_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2358_1 : adaptiveSpanWhole2358_1.domainCheck 1179 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2358_1 : adaptiveSpanWhole2358_1.spans = coreWholeSpans 0 adaptiveNumericSpans2358_1 := by decide +kernel
end Erdos883Verified
