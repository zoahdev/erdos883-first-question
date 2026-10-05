import Erdos883AdaptiveSpan12839Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_0 : adaptiveNumericSpans12839_0.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_0 : adaptiveSpanEven12839_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_0 : adaptiveSpanEven12839_0.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_0 : adaptiveSpanEven12839_0.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_0 : adaptiveSpanWhole12839_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_0 : adaptiveSpanWhole12839_0.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_0 : adaptiveSpanWhole12839_0.spans = coreWholeSpans 0 adaptiveNumericSpans12839_0 := by
  decide +kernel
end Erdos883Verified
