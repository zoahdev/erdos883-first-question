import Erdos883AdaptiveSpan10609Level6TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength10609_6 : adaptiveNumericSpans10609_6.length = 364 := by decide +kernel
theorem adaptiveSpanEvenCache10609_6 : adaptiveSpanEven10609_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain10609_6 : adaptiveSpanEven10609_6.domainCheck 5305 = true := by decide +kernel
theorem adaptiveSpanEvenEntries10609_6 : adaptiveSpanEven10609_6.spans = coreEvenSpans 5305 0 adaptiveNumericSpans10609_6 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength10609_6]
  decide
theorem adaptiveSpanWholeCache10609_6 : adaptiveSpanWhole10609_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain10609_6 : adaptiveSpanWhole10609_6.domainCheck 5305 = true := by decide +kernel
theorem adaptiveSpanWholeEntries10609_6 : adaptiveSpanWhole10609_6.spans = coreWholeSpans 0 adaptiveNumericSpans10609_6 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength10609_6]
  decide
end Erdos883Verified
