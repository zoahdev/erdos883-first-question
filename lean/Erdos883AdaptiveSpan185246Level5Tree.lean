import Erdos883AdaptiveSpan185246Level5TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength185246_5 : adaptiveNumericSpans185246_5.length = 769 := by decide +kernel
theorem adaptiveSpanEvenCache185246_5 : adaptiveSpanEven185246_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain185246_5 : adaptiveSpanEven185246_5.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanEvenEntries185246_5 : adaptiveSpanEven185246_5.spans = coreEvenSpans 92623 0 adaptiveNumericSpans185246_5 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength185246_5]
  decide
theorem adaptiveSpanWholeCache185246_5 : adaptiveSpanWhole185246_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain185246_5 : adaptiveSpanWhole185246_5.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanWholeEntries185246_5 : adaptiveSpanWhole185246_5.spans = coreWholeSpans 0 adaptiveNumericSpans185246_5 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength185246_5]
  decide
end Erdos883Verified
