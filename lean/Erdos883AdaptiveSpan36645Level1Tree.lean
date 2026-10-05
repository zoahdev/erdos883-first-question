import Erdos883AdaptiveSpan36645Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength36645_1 : adaptiveNumericSpans36645_1.length = 496 := by decide +kernel
theorem adaptiveSpanEvenCache36645_1 : adaptiveSpanEven36645_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain36645_1 : adaptiveSpanEven36645_1.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanEvenEntries36645_1 : adaptiveSpanEven36645_1.spans = coreEvenSpans 18323 0 adaptiveNumericSpans36645_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache36645_1 : adaptiveSpanWhole36645_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain36645_1 : adaptiveSpanWhole36645_1.domainCheck 18323 = true := by decide +kernel
theorem adaptiveSpanWholeEntries36645_1 : adaptiveSpanWhole36645_1.spans = coreWholeSpans 0 adaptiveNumericSpans36645_1 := by
  decide +kernel
end Erdos883Verified
