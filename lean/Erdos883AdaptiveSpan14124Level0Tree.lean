import Erdos883AdaptiveSpan14124Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength14124_0 : adaptiveNumericSpans14124_0.length = 391 := by decide +kernel
theorem adaptiveSpanEvenCache14124_0 : adaptiveSpanEven14124_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain14124_0 : adaptiveSpanEven14124_0.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanEvenEntries14124_0 : adaptiveSpanEven14124_0.spans = coreEvenSpans 7062 0 adaptiveNumericSpans14124_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache14124_0 : adaptiveSpanWhole14124_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain14124_0 : adaptiveSpanWhole14124_0.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanWholeEntries14124_0 : adaptiveSpanWhole14124_0.spans = coreWholeSpans 0 adaptiveNumericSpans14124_0 := by
  decide +kernel
end Erdos883Verified
