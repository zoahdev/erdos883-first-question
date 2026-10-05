import Erdos883AdaptiveSpan12839Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_3 : adaptiveNumericSpans12839_3.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_3 : adaptiveSpanEven12839_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_3 : adaptiveSpanEven12839_3.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_3 : adaptiveSpanEven12839_3.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_3 : adaptiveSpanWhole12839_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_3 : adaptiveSpanWhole12839_3.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_3 : adaptiveSpanWhole12839_3.spans = coreWholeSpans 0 adaptiveNumericSpans12839_3 := by
  decide +kernel
end Erdos883Verified
