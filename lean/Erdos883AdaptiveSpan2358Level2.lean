import Erdos883AdaptiveCertificate2358Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2358_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 22838810403753417808093757072779857403453235808698623658180640045236504097994494554194940364983001600284712993649498573813633684320015886292646873490568501756700963903898079585091645476504231163078648743547021714945779196788594798914099277698917601739716753196955503157517777314174040444383484969088
def adaptiveNumericSpans2358_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2358_2Chunk0].flatten
def adaptiveSpanEven2358_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1179 0 adaptiveNumericSpans2358_2)
def adaptiveSpanWhole2358_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2358_2)
theorem adaptiveSpanNumericCheck2358_2 : coreNumericSpansCheck 2301 7 720 1001 adaptiveNumericSpans2358_2 adaptiveRows2358 = true := by decide +kernel
theorem adaptiveSpanEvenCache2358_2 : adaptiveSpanEven2358_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2358_2 : adaptiveSpanEven2358_2.domainCheck 1179 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2358_2 : adaptiveSpanEven2358_2.spans = coreEvenSpans 1179 0 adaptiveNumericSpans2358_2 := by decide +kernel
theorem adaptiveSpanWholeCache2358_2 : adaptiveSpanWhole2358_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2358_2 : adaptiveSpanWhole2358_2.domainCheck 1179 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2358_2 : adaptiveSpanWhole2358_2.spans = coreWholeSpans 0 adaptiveNumericSpans2358_2 := by decide +kernel
end Erdos883Verified
