import Erdos883AdaptiveSpan12839Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_5 : adaptiveNumericSpans12839_5.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_5 : adaptiveSpanEven12839_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_5 : adaptiveSpanEven12839_5.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_5 : adaptiveSpanEven12839_5.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_5 : adaptiveSpanWhole12839_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_5 : adaptiveSpanWhole12839_5.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_5 : adaptiveSpanWhole12839_5.spans = coreWholeSpans 0 adaptiveNumericSpans12839_5 := by
  decide +kernel
end Erdos883Verified
