import Erdos883AdaptiveSpan12839Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_2 : adaptiveNumericSpans12839_2.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_2 : adaptiveSpanEven12839_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_2 : adaptiveSpanEven12839_2.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_2 : adaptiveSpanEven12839_2.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_2 : adaptiveSpanWhole12839_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_2 : adaptiveSpanWhole12839_2.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_2 : adaptiveSpanWhole12839_2.spans = coreWholeSpans 0 adaptiveNumericSpans12839_2 := by
  decide +kernel
end Erdos883Verified
