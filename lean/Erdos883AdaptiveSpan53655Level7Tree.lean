import Erdos883AdaptiveSpan53655Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength53655_7 : adaptiveNumericSpans53655_7.length = 538 := by decide +kernel
theorem adaptiveSpanEvenCache53655_7 : adaptiveSpanEven53655_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain53655_7 : adaptiveSpanEven53655_7.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanEvenEntries53655_7 : adaptiveSpanEven53655_7.spans = coreEvenSpans 26828 0 adaptiveNumericSpans53655_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache53655_7 : adaptiveSpanWhole53655_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain53655_7 : adaptiveSpanWhole53655_7.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanWholeEntries53655_7 : adaptiveSpanWhole53655_7.spans = coreWholeSpans 0 adaptiveNumericSpans53655_7 := by
  decide +kernel
end Erdos883Verified
