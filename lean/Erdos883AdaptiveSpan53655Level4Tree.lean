import Erdos883AdaptiveSpan53655Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength53655_4 : adaptiveNumericSpans53655_4.length = 538 := by decide +kernel
theorem adaptiveSpanEvenCache53655_4 : adaptiveSpanEven53655_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain53655_4 : adaptiveSpanEven53655_4.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanEvenEntries53655_4 : adaptiveSpanEven53655_4.spans = coreEvenSpans 26828 0 adaptiveNumericSpans53655_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache53655_4 : adaptiveSpanWhole53655_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain53655_4 : adaptiveSpanWhole53655_4.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanWholeEntries53655_4 : adaptiveSpanWhole53655_4.spans = coreWholeSpans 0 adaptiveNumericSpans53655_4 := by
  decide +kernel
end Erdos883Verified
