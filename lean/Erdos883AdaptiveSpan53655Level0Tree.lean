import Erdos883AdaptiveSpan53655Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength53655_0 : adaptiveNumericSpans53655_0.length = 538 := by decide +kernel
theorem adaptiveSpanEvenCache53655_0 : adaptiveSpanEven53655_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain53655_0 : adaptiveSpanEven53655_0.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanEvenEntries53655_0 : adaptiveSpanEven53655_0.spans = coreEvenSpans 26828 0 adaptiveNumericSpans53655_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache53655_0 : adaptiveSpanWhole53655_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain53655_0 : adaptiveSpanWhole53655_0.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanWholeEntries53655_0 : adaptiveSpanWhole53655_0.spans = coreWholeSpans 0 adaptiveNumericSpans53655_0 := by
  decide +kernel
end Erdos883Verified
