import Erdos883AdaptiveSpan185246Level7TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength185246_7 : adaptiveNumericSpans185246_7.length = 769 := by decide +kernel
theorem adaptiveSpanEvenCache185246_7 : adaptiveSpanEven185246_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain185246_7 : adaptiveSpanEven185246_7.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanEvenEntries185246_7 : adaptiveSpanEven185246_7.spans = coreEvenSpans 92623 0 adaptiveNumericSpans185246_7 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength185246_7]
  decide
theorem adaptiveSpanWholeCache185246_7 : adaptiveSpanWhole185246_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain185246_7 : adaptiveSpanWhole185246_7.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanWholeEntries185246_7 : adaptiveSpanWhole185246_7.spans = coreWholeSpans 0 adaptiveNumericSpans185246_7 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength185246_7]
  decide
end Erdos883Verified
