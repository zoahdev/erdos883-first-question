import Erdos883AdaptiveCertificate2358Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2358_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 36700553323409397270371677542453444031846740747665664939477070933516165423075739626072102960173708245421304895267644734542531813397125304089561894341525980390550616611171853511670518755668031393140771488035059695448081456725602692410229319677892631089468192060566976643423094021434729596424446621576838346628646325159398608797062541008035389470256675814375552
def adaptiveNumericSpans2358_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2358_3Chunk0].flatten
def adaptiveSpanEven2358_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1179 0 adaptiveNumericSpans2358_3)
def adaptiveSpanWhole2358_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2358_3)
theorem adaptiveSpanNumericCheck2358_3 : coreNumericSpansCheck 2301 7 120 143 adaptiveNumericSpans2358_3 adaptiveRows2358 = true := by decide +kernel
theorem adaptiveSpanEvenCache2358_3 : adaptiveSpanEven2358_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2358_3 : adaptiveSpanEven2358_3.domainCheck 1179 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2358_3 : adaptiveSpanEven2358_3.spans = coreEvenSpans 1179 0 adaptiveNumericSpans2358_3 := by decide +kernel
theorem adaptiveSpanWholeCache2358_3 : adaptiveSpanWhole2358_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2358_3 : adaptiveSpanWhole2358_3.domainCheck 1179 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2358_3 : adaptiveSpanWhole2358_3.spans = coreWholeSpans 0 adaptiveNumericSpans2358_3 := by decide +kernel
end Erdos883Verified
