import Erdos883AdaptiveSpan14124Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength14124_3 : adaptiveNumericSpans14124_3.length = 391 := by decide +kernel
theorem adaptiveSpanEvenCache14124_3 : adaptiveSpanEven14124_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain14124_3 : adaptiveSpanEven14124_3.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanEvenEntries14124_3 : adaptiveSpanEven14124_3.spans = coreEvenSpans 7062 0 adaptiveNumericSpans14124_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache14124_3 : adaptiveSpanWhole14124_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain14124_3 : adaptiveSpanWhole14124_3.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanWholeEntries14124_3 : adaptiveSpanWhole14124_3.spans = coreWholeSpans 0 adaptiveNumericSpans14124_3 := by
  decide +kernel
end Erdos883Verified
