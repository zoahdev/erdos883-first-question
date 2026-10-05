import Erdos883AdaptiveSpan48777Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_4 : adaptiveNumericSpans48777_4.length = 525 := by decide +kernel
theorem adaptiveSpanEvenCache48777_4 : adaptiveSpanEven48777_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_4 : adaptiveSpanEven48777_4.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_4 : adaptiveSpanEven48777_4.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_4 : adaptiveSpanWhole48777_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_4 : adaptiveSpanWhole48777_4.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_4 : adaptiveSpanWhole48777_4.spans = coreWholeSpans 0 adaptiveNumericSpans48777_4 := by
  decide +kernel
end Erdos883Verified
