import Erdos883AdaptiveSpan59021Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_8 : adaptiveNumericSpans59021_8.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_8 : adaptiveSpanEven59021_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_8 : adaptiveSpanEven59021_8.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_8 : adaptiveSpanEven59021_8.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_8 : adaptiveSpanWhole59021_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_8 : adaptiveSpanWhole59021_8.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_8 : adaptiveSpanWhole59021_8.spans = coreWholeSpans 0 adaptiveNumericSpans59021_8 := by
  decide +kernel
end Erdos883Verified
