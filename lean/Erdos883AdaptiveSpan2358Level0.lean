import Erdos883AdaptiveCertificate2358Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2358_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 36700553323409397270371677542453444031846740747665664939477070933516165423075739626072102960173708245421304895267644734542531813397125304089561894341525212872340983483765759238219459634685237831663410039083297247240598686787785647355030509982296249305639471511940946565514702416367252619018562554100888584809672198098369783346171499549601427436057588624523392
def adaptiveNumericSpans2358_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2358_0Chunk0].flatten
def adaptiveSpanEven2358_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1179 0 adaptiveNumericSpans2358_0)
def adaptiveSpanWhole2358_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2358_0)
theorem adaptiveSpanNumericCheck2358_0 : coreNumericSpansCheck 2301 7 480 1155 adaptiveNumericSpans2358_0 adaptiveRows2358 = true := by decide +kernel
theorem adaptiveSpanEvenCache2358_0 : adaptiveSpanEven2358_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2358_0 : adaptiveSpanEven2358_0.domainCheck 1179 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2358_0 : adaptiveSpanEven2358_0.spans = coreEvenSpans 1179 0 adaptiveNumericSpans2358_0 := by decide +kernel
theorem adaptiveSpanWholeCache2358_0 : adaptiveSpanWhole2358_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2358_0 : adaptiveSpanWhole2358_0.domainCheck 1179 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2358_0 : adaptiveSpanWhole2358_0.spans = coreWholeSpans 0 adaptiveNumericSpans2358_0 := by decide +kernel
end Erdos883Verified
