import Erdos883AdaptiveSpan36645Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_7 : adaptiveNumericSpans36645_7.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_7 : adaptiveSpanEven36645_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_7 : adaptiveSpanEven36645_7.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_7 : adaptiveSpanEven36645_7.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_7 : adaptiveSpanWhole36645_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_7 : adaptiveSpanWhole36645_7.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_7 : adaptiveSpanWhole36645_7.spans = coreWholeSpans 0 adaptiveNumericSpans36645_7 := by
  decide +kernel
end Erdos883Verified
