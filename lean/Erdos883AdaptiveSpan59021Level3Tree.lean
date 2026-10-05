import Erdos883AdaptiveSpan59021Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_3 : adaptiveNumericSpans59021_3.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_3 : adaptiveSpanEven59021_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_3 : adaptiveSpanEven59021_3.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_3 : adaptiveSpanEven59021_3.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_3 : adaptiveSpanWhole59021_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_3 : adaptiveSpanWhole59021_3.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_3 : adaptiveSpanWhole59021_3.spans = coreWholeSpans 0 adaptiveNumericSpans59021_3 := by
  decide +kernel
end Erdos883Verified
