import Erdos883AdaptiveSpan185246Level0TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength185246_0 : adaptiveNumericSpans185246_0.length = 769 := by decide +kernel
theorem adaptiveSpanEvenCache185246_0 : adaptiveSpanEven185246_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain185246_0 : adaptiveSpanEven185246_0.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanEvenEntries185246_0 : adaptiveSpanEven185246_0.spans = coreEvenSpans 92623 0 adaptiveNumericSpans185246_0 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength185246_0]
  decide
theorem adaptiveSpanWholeCache185246_0 : adaptiveSpanWhole185246_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain185246_0 : adaptiveSpanWhole185246_0.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanWholeEntries185246_0 : adaptiveSpanWhole185246_0.spans = coreWholeSpans 0 adaptiveNumericSpans185246_0 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength185246_0]
  decide
end Erdos883Verified
