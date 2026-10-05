import Erdos883AdaptiveSpan53655Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength53655_3 : adaptiveNumericSpans53655_3.length = 538 := by decide +kernel
theorem adaptiveSpanEvenCache53655_3 : adaptiveSpanEven53655_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain53655_3 : adaptiveSpanEven53655_3.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanEvenEntries53655_3 : adaptiveSpanEven53655_3.spans = coreEvenSpans 26828 0 adaptiveNumericSpans53655_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache53655_3 : adaptiveSpanWhole53655_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain53655_3 : adaptiveSpanWhole53655_3.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanWholeEntries53655_3 : adaptiveSpanWhole53655_3.spans = coreWholeSpans 0 adaptiveNumericSpans53655_3 := by
  decide +kernel
end Erdos883Verified
