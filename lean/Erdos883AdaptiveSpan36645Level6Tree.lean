import Erdos883AdaptiveSpan36645Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_6 : adaptiveNumericSpans36645_6.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_6 : adaptiveSpanEven36645_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_6 : adaptiveSpanEven36645_6.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_6 : adaptiveSpanEven36645_6.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_6 : adaptiveSpanWhole36645_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_6 : adaptiveSpanWhole36645_6.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_6 : adaptiveSpanWhole36645_6.spans = coreWholeSpans 0 adaptiveNumericSpans36645_6 := by
  decide +kernel
end Erdos883Verified
