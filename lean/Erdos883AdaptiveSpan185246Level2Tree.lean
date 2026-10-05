import Erdos883AdaptiveSpan185246Level2TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength185246_2 : adaptiveNumericSpans185246_2.length = 769 := by decide +kernel
theorem adaptiveSpanEvenCache185246_2 : adaptiveSpanEven185246_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain185246_2 : adaptiveSpanEven185246_2.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanEvenEntries185246_2 : adaptiveSpanEven185246_2.spans = coreEvenSpans 92623 0 adaptiveNumericSpans185246_2 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength185246_2]
  decide
theorem adaptiveSpanWholeCache185246_2 : adaptiveSpanWhole185246_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain185246_2 : adaptiveSpanWhole185246_2.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanWholeEntries185246_2 : adaptiveSpanWhole185246_2.spans = coreWholeSpans 0 adaptiveNumericSpans185246_2 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength185246_2]
  decide
end Erdos883Verified
