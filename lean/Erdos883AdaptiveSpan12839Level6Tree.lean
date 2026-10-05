import Erdos883AdaptiveSpan12839Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_6 : adaptiveNumericSpans12839_6.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_6 : adaptiveSpanEven12839_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_6 : adaptiveSpanEven12839_6.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_6 : adaptiveSpanEven12839_6.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_6 : adaptiveSpanWhole12839_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_6 : adaptiveSpanWhole12839_6.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_6 : adaptiveSpanWhole12839_6.spans = coreWholeSpans 0 adaptiveNumericSpans12839_6 := by
  decide +kernel
end Erdos883Verified
