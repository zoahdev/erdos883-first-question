import Erdos883AdaptiveSpan12839Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_8 : adaptiveNumericSpans12839_8.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_8 : adaptiveSpanEven12839_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_8 : adaptiveSpanEven12839_8.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_8 : adaptiveSpanEven12839_8.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_8 : adaptiveSpanWhole12839_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_8 : adaptiveSpanWhole12839_8.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_8 : adaptiveSpanWhole12839_8.spans = coreWholeSpans 0 adaptiveNumericSpans12839_8 := by
  decide +kernel
end Erdos883Verified
