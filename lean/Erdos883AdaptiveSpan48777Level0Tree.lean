import Erdos883AdaptiveSpan48777Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_0 : adaptiveNumericSpans48777_0.length = 525 := by decide +kernel
theorem adaptiveSpanEvenCache48777_0 : adaptiveSpanEven48777_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_0 : adaptiveSpanEven48777_0.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_0 : adaptiveSpanEven48777_0.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_0 : adaptiveSpanWhole48777_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_0 : adaptiveSpanWhole48777_0.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_0 : adaptiveSpanWhole48777_0.spans = coreWholeSpans 0 adaptiveNumericSpans48777_0 := by
  decide +kernel
end Erdos883Verified
