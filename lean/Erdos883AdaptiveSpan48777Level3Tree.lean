import Erdos883AdaptiveSpan48777Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_3 : adaptiveNumericSpans48777_3.length = 525 := by decide +kernel
theorem adaptiveSpanEvenCache48777_3 : adaptiveSpanEven48777_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_3 : adaptiveSpanEven48777_3.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_3 : adaptiveSpanEven48777_3.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_3 : adaptiveSpanWhole48777_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_3 : adaptiveSpanWhole48777_3.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_3 : adaptiveSpanWhole48777_3.spans = coreWholeSpans 0 adaptiveNumericSpans48777_3 := by
  decide +kernel
end Erdos883Verified
