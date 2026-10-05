import Erdos883AdaptiveSpan12839Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_4 : adaptiveNumericSpans12839_4.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_4 : adaptiveSpanEven12839_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_4 : adaptiveSpanEven12839_4.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_4 : adaptiveSpanEven12839_4.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_4 : adaptiveSpanWhole12839_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_4 : adaptiveSpanWhole12839_4.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_4 : adaptiveSpanWhole12839_4.spans = coreWholeSpans 0 adaptiveNumericSpans12839_4 := by
  decide +kernel
end Erdos883Verified
