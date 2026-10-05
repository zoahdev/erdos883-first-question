import Erdos883AdaptiveSpan11671Level0TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength11671_0 : adaptiveNumericSpans11671_0.length = 375 := by decide +kernel
theorem adaptiveSpanEvenCache11671_0 : adaptiveSpanEven11671_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain11671_0 : adaptiveSpanEven11671_0.domainCheck 5836 = true := by decide +kernel
theorem adaptiveSpanEvenEntries11671_0 : adaptiveSpanEven11671_0.spans = coreEvenSpans 5836 0 adaptiveNumericSpans11671_0 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength11671_0]
  decide
theorem adaptiveSpanWholeCache11671_0 : adaptiveSpanWhole11671_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain11671_0 : adaptiveSpanWhole11671_0.domainCheck 5836 = true := by decide +kernel
theorem adaptiveSpanWholeEntries11671_0 : adaptiveSpanWhole11671_0.spans = coreWholeSpans 0 adaptiveNumericSpans11671_0 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength11671_0]
  decide
end Erdos883Verified
