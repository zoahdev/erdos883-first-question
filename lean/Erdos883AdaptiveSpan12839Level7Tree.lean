import Erdos883AdaptiveSpan12839Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_7 : adaptiveNumericSpans12839_7.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_7 : adaptiveSpanEven12839_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_7 : adaptiveSpanEven12839_7.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_7 : adaptiveSpanEven12839_7.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_7 : adaptiveSpanWhole12839_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_7 : adaptiveSpanWhole12839_7.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_7 : adaptiveSpanWhole12839_7.spans = coreWholeSpans 0 adaptiveNumericSpans12839_7 := by
  decide +kernel
end Erdos883Verified
